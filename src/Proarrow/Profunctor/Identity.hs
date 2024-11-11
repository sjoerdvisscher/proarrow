module Proarrow.Profunctor.Identity where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Category.Dagger (DaggerProfunctor (..), Dagger)

type Id :: CAT k
newtype Id a b = Id {unId :: a ~> b}

instance (CategoryOf k) => Profunctor (Id :: CAT k) where
  dimap l r (Id f) = Id (r . f . l)
  r \\ Id f = r \\ f

instance (CategoryOf k) => Promonad (Id :: CAT k) where
  id = Id id
  Id f . Id g = Id (f . g)

instance (CategoryOf k) => Representable (Id :: CAT k) where
  type Id % a = a
  index = unId
  tabulate = Id
  repMap = id

instance (CategoryOf k) => Corepresentable (Id :: CAT k) where
  type Id %% a = a
  coindex = unId
  cotabulate = Id
  corepMap = id

instance (Monoidal k) => MonoidalProfunctor (Id :: CAT k) where
  par0 = Id par0
  Id f `par` Id g = Id (f `par` g)

instance (Dagger k) => DaggerProfunctor (Id :: CAT k) where
  dagger (Id p) = Id (dagger p)