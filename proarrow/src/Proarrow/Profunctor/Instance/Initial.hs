module Proarrow.Profunctor.Instance.Initial where

import Prelude (Eq, Show)

import Proarrow.Category.Enriched.Dagger (Dagger, DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin (Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Zero (Bottom (..))
import Proarrow.Core (CategoryOf, Profunctor (..), type (+->))

type InitialProfunctor :: j +-> k
data InitialProfunctor a b
  deriving (Show, Eq)

instance (CategoryOf j, CategoryOf k) => Profunctor (InitialProfunctor :: j +-> k) where
  dimap _ _ = \case {}
  (\\) _ = \case {}

instance (Dagger k) => DaggerProfunctor (InitialProfunctor :: k +-> k) where
  dagger = \case {}

instance (Thin j, Thin k) => (ThinProfunctor (InitialProfunctor :: j +-> k)) where
  type HasArrow (InitialProfunctor :: j +-> k) a b = Bottom
  arr = no
  withArr = \case {}