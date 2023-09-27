module Proarrow.Category.Instance.Zero where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)

data VOID

type Zero :: CAT VOID
data Zero a b

type instance (~>) = Zero

class IsVoid (a :: VOID) where
  voidId :: Zero a a

-- | The category with no objects, the initial category.
instance Category Zero where
  type Ob a = IsVoid a
  id = voidId
  (.) = \case

instance Profunctor Zero where
  dimap = dimapDefault
  _ \\ x = case x of