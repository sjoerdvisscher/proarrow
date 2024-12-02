module Proarrow.Profunctor.Initial where

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Core (CategoryOf, Profunctor (..), type (+->))

type InitialProfunctor :: j +-> k
data InitialProfunctor a b

instance (CategoryOf j, CategoryOf k) => Profunctor (InitialProfunctor :: j +-> k) where
  dimap _ _ = \case {}
  (\\) _ = \case {}

instance (CategoryOf k) => DaggerProfunctor (InitialProfunctor :: k +-> k) where
  dagger = \case {}
