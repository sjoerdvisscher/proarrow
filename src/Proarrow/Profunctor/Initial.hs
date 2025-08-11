module Proarrow.Profunctor.Initial where

import Proarrow.Category.Enriched.Dagger (Dagger, DaggerProfunctor (..))
import Proarrow.Core (CategoryOf, Profunctor (..), type (+->))
import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..), Thin)
import Proarrow.Category.Instance.Zero (Bottom (..))

type InitialProfunctor :: j +-> k
data InitialProfunctor a b

instance (CategoryOf j, CategoryOf k) => Profunctor (InitialProfunctor :: j +-> k) where
  dimap _ _ = \case {}
  (\\) _ = \case {}

instance (Dagger k) => DaggerProfunctor (InitialProfunctor :: k +-> k) where
  dagger = \case {}

instance (Thin j, Thin k) => (ThinProfunctor (InitialProfunctor :: j +-> k)) where
  type HasArrow (InitialProfunctor :: j +-> k) a b = Bottom
  arr = no
  withArr = \case {}