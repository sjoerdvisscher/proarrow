module Proarrow.Promonad.Collage where

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>), lmap, rmap)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT(..), (:++:)(..), coproductId)
import Proarrow.Functor (Functor(..))
import Proarrow.Promonad (Promonad(..))

type Collage :: PRO j k -> PRO (COPRODUCT j k) (COPRODUCT j k)
data Collage p a b where
  InL :: (a ~> b) -> Collage p (L a) (L b)
  InR :: (a ~> b) -> Collage p (R a) (R b)
  L2R :: p a b -> Collage p (L a) (R b)

instance Profunctor p => Profunctor (Collage p) where
  dimap (InjL l) (InjL r) (InL f) = InL (dimap l r f)
  dimap (InjR l) (InjR r) (InR f) = InR (dimap l r f)
  dimap (InjL l) (InjR r) (L2R p) = L2R (dimap l r p)
  dimap (InjR _) (InjL _) f = case f of
  r \\ InL f = r \\ f
  r \\ InR f = r \\ f
  r \\ L2R p = r \\ p

instance Profunctor p => Promonad (Collage p) where
  unit :: forall a. Ob a => Collage p a a
  unit = case coproductId @a of
    InjL f -> InL f
    InjR f -> InR f
  mult (InL g) (InL f) = InL (f . g)
  mult (InL g) (L2R p) = L2R (lmap g p)
  mult (L2R p) (InR f) = L2R (rmap f p)
  mult (InR g) (InR f) = InR (f . g)

instance Functor Collage where
  map (Prof n) = Prof \case
    InL l -> InL l
    InR r -> InR r
    L2R p -> L2R (n p)