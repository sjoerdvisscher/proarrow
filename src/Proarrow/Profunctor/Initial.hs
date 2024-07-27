module Proarrow.Profunctor.Initial where

import Proarrow.Core (CategoryOf, PRO, Profunctor (..))

type InitialProfunctor :: PRO j k
data InitialProfunctor a b

instance (CategoryOf j, CategoryOf k) => Profunctor (InitialProfunctor :: PRO j k) where
  dimap _ _ = \case {}
  (\\) _ = \case {}
