-- | The identity profunctor 'Id', wrapping the hom arrows of a category. It is the unit of profunctor
-- composition ("Proarrow.Profunctor.Instance.Composition") and the identity 'Promonad'.
module Proarrow.Profunctor.Instance.Identity where

import Proarrow.Category.Enriched.Dagger (Dagger, DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..))
import Proarrow.Functor (FunctorForRep (..))

type Id :: CAT k
newtype Id a b = Id {unId :: a ~> b}

instance (CategoryOf k) => Profunctor (Id :: CAT k) where
  dimap l r (Id f) = Id (r . f . l)
  r \\ Id f = r \\ f

instance (CategoryOf k) => Promonad (Id :: CAT k) where
  id = Id id
  Id f . Id g = Id (f . g)

instance (CategoryOf k) => FunctorForRep (Id :: CAT k) where
  type Id @ a = a
  fmap f = f

instance (Dagger k) => DaggerProfunctor (Id :: CAT k) where
  dagger (Id p) = Id (dagger p)

instance (Thin k) => ThinProfunctor (Id :: CAT k) where
  type HasArrow (Id :: CAT k) a b = HasArrow (Hom k) a b
  arr = Id arr
  withArr (Id f) r = withArr f r
