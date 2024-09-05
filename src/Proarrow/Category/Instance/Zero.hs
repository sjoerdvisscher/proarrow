module Proarrow.Category.Instance.Zero where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Preorder.ThinCategory (Thin (..))

data VOID

type Zero :: CAT VOID
data Zero a b

class IsVoid (a :: VOID) where
  voidArr :: Zero a b

-- | The category with no objects, the initial category.
instance CategoryOf VOID where
  type (~>) = Zero
  type Ob a = IsVoid a

instance Promonad Zero where
  id = voidArr
  (.) = \case {}

instance Profunctor Zero where
  dimap = dimapDefault
  _ \\ x = case x of {}

instance Thin VOID where
  type HasArrow a b = IsVoid a
  arr = voidArr
  withArr = \case {}