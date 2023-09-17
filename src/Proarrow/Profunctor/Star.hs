module Proarrow.Profunctor.Star where

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>))
import Proarrow.Functor (Functor(..))
import Proarrow.Profunctor.Representable (Representable(..))

type Star :: (k1 -> k2) -> PRO k2 k1
data Star f a b where
  Star :: Ob b => { getStar :: a ~> f b } -> Star f a b

instance Functor f => Profunctor (Star f) where
  dimap l r (Star f) = Star (map @f r . f . l) \\ r
  r \\ Star f = r \\ f

instance Functor f => Representable (Star f) where
  type Star f % a = f a
  index = getStar
  tabulate = Star
  repMap = map
