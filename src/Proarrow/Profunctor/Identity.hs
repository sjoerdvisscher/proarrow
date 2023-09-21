module Proarrow.Profunctor.Identity where

import Proarrow.Core (CAT, CategoryOf, Category(..), Profunctor(..), type (~>))
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Profunctor.Corepresentable (Corepresentable(..))

type Id :: CAT k
newtype Id a b = Id { getId :: a ~> b }

instance CategoryOf k => Profunctor (Id :: CAT k) where
  dimap l r (Id f) = Id (r . f . l)
  r \\ Id f = r \\ f

instance CategoryOf k => Representable (Id :: CAT k) where
  type Id % a = a
  index = getId
  tabulate = Id
  repMap = id

instance CategoryOf k => Corepresentable (Id :: CAT k) where
  type Id %% a = a
  coindex = getId
  cotabulate = Id
  corepMap = id
