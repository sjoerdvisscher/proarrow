module Proarrow.Profunctor.Identity where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Representable (..))

type Id :: CAT k
newtype Id a b = Id {getId :: a ~> b}

instance (CategoryOf k) => Profunctor (Id :: CAT k) where
  dimap l r (Id f) = Id (r . f . l)
  r \\ Id f = r \\ f

instance (CategoryOf k) => Promonad (Id :: CAT k) where
  id = Id id
  Id f . Id g = Id (f . g)

instance (CategoryOf k) => Representable (Id :: CAT k) where
  type Id % a = a
  index = getId
  tabulate = Id
  repMap = id

instance (CategoryOf k) => Corepresentable (Id :: CAT k) where
  type Id %% a = a
  coindex = getId
  cotabulate = Id
  corepMap = id
