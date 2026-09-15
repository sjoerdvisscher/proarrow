-- | The empty profunctor, with no values at all: the initial object of the category of profunctors
-- @j +-> k@.
module Proarrow.Profunctor.Instance.Initial where

import Prelude (Eq, Show)

import Proarrow.Category.Enriched.Dagger (Dagger, DaggerProfunctor (..))
import Proarrow.Category.Enriched.Thin (DecidableProfunctor (..), Decision (..), Thin, ThinProfunctor (..))
import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Category.Instance.Zero (Bottom (..))
import Proarrow.Core (CategoryOf, Profunctor (..), type (+->))

-- | The profunctor with no values at all: the initial object of the category of profunctors
-- @j +-> k@.
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

instance (Thin j, Thin k) => DecidableProfunctor (InitialProfunctor :: j +-> k) where
  type Holds (InitialProfunctor :: j +-> k) a b = FLS
  decide = No
  toHolds = \case {}
