module Proarrow.Profunctor.Instance.Cocone where

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Colimit.BinaryCoproduct (COPROD (..), Coprod (..), HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, rmap, type (+->))
import Proarrow.Profunctor.Instance.List (LIST (..), List (..))

-- | A cocone is a bunch of arrows with a shared target.
data Cocone (bs :: LIST k) (a :: COPROD k) where
  Coapex :: (Ob a) => Cocone (L '[]) (COPR a)
  Coleg :: b ~> a -> Cocone (L bs) (COPR a) -> Cocone (L (b : bs)) (COPR a)

instance (CategoryOf k) => Profunctor (Cocone :: COPROD k +-> LIST k) where
  dimap Nil r Coapex = Coapex \\ r
  dimap (Cons l ls) r@(Coprod r') (Coleg f fs) = Coleg (r' . f . l) (dimap ls r fs)
  r \\ Coapex = r
  r \\ Coleg l Coapex = r \\ l
  r \\ Coleg l c@(Coleg _ c1) = r \\ l \\ c \\ c1

instance (HasCoproducts k) => MonoidalProfunctor (Cocone :: COPROD k +-> LIST k) where
  one = Coapex
  Coapex @l ** rs = rmap (Coprod (rgt @_ @l)) rs \\ rs
  Coleg l ls ** (rs :: Cocone rs r) = Coleg (lft @_ @_ @(UN COPR r) . l) (ls ** rs) \\ l \\ rs

-- | A sink is a cocone, but with the apex type hidden by an existential.
data Sink (as :: [k]) where
  Cocone :: Cocone (L as) (COPR a) -> Sink as
