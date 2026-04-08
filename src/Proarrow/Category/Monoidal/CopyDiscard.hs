{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal.CopyDiscard where

import Data.Kind (Type)

import Proarrow.Category (Supplies)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Sub (SUBCAT, Sub (..), SubMonoidal)
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CategoryOf (..), OB)
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Object.BinaryProduct (HasProducts, PROD (..))

class (Monoidal k) => CopyDiscard k where
  copy :: (Ob (a :: k)) => a ~> a ** a
  default copy :: (k `Supplies` Comonoid) => (Ob (a :: k)) => a ~> a ** a
  copy = comult
  discard :: (Ob (a :: k)) => a ~> Unit
  default discard :: (k `Supplies` Comonoid) => (Ob (a :: k)) => a ~> Unit
  discard = counit

instance (HasProducts k) => CopyDiscard (PROD k)
instance CopyDiscard Type
instance CopyDiscard ()
instance (CopyDiscard j, CopyDiscard k) => CopyDiscard (j, k) where
  copy = copy :**: copy
  discard = discard :**: discard

instance (SubMonoidal ob, CopyDiscard k) => CopyDiscard (SUBCAT (ob :: OB k)) where
  copy = Sub copy
  discard = Sub discard
