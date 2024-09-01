{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Bicategory.Terminal where

import Data.Type.Equality (type (~), type (~~))

import Proarrow.Category.Bicategory (Bicategory (..), Monad (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)

type Terminal :: CAT (Unit j k)
data Terminal a b where
  Terminal :: Terminal 'Unit 'Unit

instance Profunctor (Terminal :: CAT (Unit '() '())) where
  dimap = dimapDefault
  r \\ Terminal = r
instance Promonad (Terminal :: CAT (Unit '() '())) where
  id = Terminal
  Terminal . Terminal = Terminal
instance (j ~ '(), k ~ '()) => CategoryOf (Unit j k) where
  type (~>) = Terminal
  type Ob @(Unit j k) p = (p ~~ 'Unit)

instance Bicategory Unit where
  type Ob0 Unit k = (k ~ '())
  type I = 'Unit
  type O a b = 'Unit
  r \\\ Terminal = r
  Terminal `o` Terminal = Terminal
  leftUnitor Terminal = Terminal
  leftUnitorInv Terminal = Terminal
  rightUnitor Terminal = Terminal
  rightUnitorInv Terminal = Terminal
  associator Terminal Terminal Terminal = Terminal
  associatorInv Terminal Terminal Terminal = Terminal

instance Monad 'Unit where
  eta = Terminal
  mu = Terminal
