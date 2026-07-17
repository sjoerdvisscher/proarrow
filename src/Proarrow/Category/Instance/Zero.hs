{-# OPTIONS_GHC -Wno-missing-methods #-}

module Proarrow.Category.Instance.Zero where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, type (+->))
import Proarrow.Functor (FunctorForRep (..))

type data VOID

type Zero :: CAT VOID
data Zero a b

-- Stolen from the constraints package
class Bottom where
  no :: a

-- | The category with no objects, the initial category.
instance CategoryOf VOID where
  type (~>) = Zero
  type Ob a = Bottom

instance Promonad Zero where
  id = no
  (.) = \case {}

instance Profunctor Zero where
  dimap = dimapDefault
  _ \\ x = case x of {}

instance DaggerProfunctor Zero where
  dagger = \case {}

data family Absurd :: VOID +-> k
instance (CategoryOf k) => FunctorForRep (Absurd :: VOID +-> k) where
  fmap = \case {}