module Proarrow.Profunctor.Cone where

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, lmap, type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Prod (..))
import Proarrow.Profunctor.List (LIST (..), List (..))

-- | A cone is a bunch of arrows with a shared source.
data Cone (a :: PROD k) (bs :: LIST k) where
  Apex :: (Ob a) => Cone (PR a) (L '[])
  Leg :: a ~> b -> Cone (PR a) (L bs) -> Cone (PR a) (L (b : bs))

instance (CategoryOf k) => Profunctor (Cone :: LIST k +-> PROD k) where
  dimap l Nil Apex = Apex \\ l
  dimap (Prod l) (Cons r rs) (Leg f fs) = Leg (r . f . l) (dimap (Prod l) rs fs)
  r \\ Apex = r
  r \\ Leg l Apex = r \\ l
  r \\ Leg l c@(Leg _ c1) = r \\ l \\ c \\ c1

instance (HasProducts k) => MonoidalProfunctor (Cone :: LIST k +-> PROD k) where
  one = Apex
  Apex @a ** rs = lmap (Prod (snd @_ @a)) rs \\ rs
  Leg l ls ** (rs :: Cone r rs) = Leg (l . fst @_ @_ @(UN PR r)) (ls ** rs) \\ l \\ rs

-- | A cosink (a.k.a a source) is a cone, but with the apex type hidden by an existential.
data Cosink (as :: [k]) where
  Cone :: Cone (PR a) (L as) -> Cosink as