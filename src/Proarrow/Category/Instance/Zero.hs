module Proarrow.Category.Instance.Zero where

import Proarrow.Core (CAT, CategoryOf(..), Promonad(..), Profunctor(..), dimapDefault)

data VOID

type Zero :: CAT VOID
data Zero a b

class IsVoid (a :: VOID) where
  voidId :: Zero a a

-- | The category with no objects, the initial category.
instance CategoryOf VOID where
  type (~>) = Zero
  type Ob a = IsVoid a

instance Promonad Zero where
  id = voidId
  (.) = \case

instance Profunctor Zero where
  dimap = dimapDefault
  _ \\ x = case x of