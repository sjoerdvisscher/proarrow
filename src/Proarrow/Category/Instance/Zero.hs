module Proarrow.Category.Instance.Zero where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Preorder.ThinCategory (ThinProfunctor (..))

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

instance ThinProfunctor Zero where
  arr = no
  withArr = \case {}