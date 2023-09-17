module Proarrow.Promonad.Collage where

import Prelude (Either(..))

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>), lmap, rmap)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Coproduct ((:++:)(..))
import Proarrow.Functor (Functor(..))
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Promonad (Promonad(..))

type Collage :: PRO k1 k2 -> PRO (Either k1 k2) (Either k1 k2)
data Collage p a b where
  InL :: (a ~> b) -> Collage p ('Left a) ('Left b)
  InR :: (a ~> b) -> Collage p ('Right a) ('Right b)
  L2R :: p a b -> Collage p ('Left a) ('Right b)
instance Profunctor p => Profunctor (Collage p) where
  dimap (L l) (L r) (InL f) = InL (dimap l r f)
  dimap (R l) (R r) (InR f) = InR (dimap l r f)
  dimap (L l) (R r) (L2R p) = L2R (dimap l r p)
  dimap (R _) (L _) f = case f of
  r \\ InL f = r \\ f
  r \\ InR f = r \\ f
  r \\ L2R p = r \\ p
instance Profunctor p => Promonad (Collage p) where
  unit (L f) = InL f
  unit (R g) = InR g
  mult (InL f :.: InL g) = InL (f . g)
  mult (L2R p :.: InL g) = L2R (lmap g p)
  mult (InR f :.: L2R p) = L2R (rmap f p)
  mult (InR f :.: InR g) = InR (f . g)
instance Functor Collage where
  map (Prof n) = Prof \case
    InL l -> InL l
    InR r -> InR r
    L2R p -> L2R (n p)