{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Terminal where

import Data.Type.Equality (type (~), type (~~))

import Proarrow.Category.Bicategory (Bicategory (..), Monad (..))
import Proarrow.Category.Instance.Unit ()
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)

type TERMK :: CAT ()
data TERMK j k where
  T1 :: TERMK '() '()

type Terminal :: CAT (TERMK j k)
data Terminal a b where
  Terminal :: Terminal T1 T1

instance Profunctor (Terminal :: CAT (TERMK '() '())) where
  dimap = dimapDefault
  r \\ Terminal = r
instance Promonad (Terminal :: CAT (TERMK '() '())) where
  id = Terminal
  Terminal . Terminal = Terminal
instance (j ~ '(), k ~ '()) => CategoryOf (TERMK j k) where
  type (~>) = Terminal
  type Ob @(TERMK j k) p = (p ~~ T1)

instance Bicategory TERMK where
  type Ob0 TERMK k = (k ~ '())
  type I = T1
  type O a b = T1
  r \\\ Terminal = r
  Terminal `o` Terminal = Terminal
  leftUnitor Terminal = Terminal
  leftUnitorInv Terminal = Terminal
  rightUnitor Terminal = Terminal
  rightUnitorInv Terminal = Terminal
  associator Terminal Terminal Terminal = Terminal
  associatorInv Terminal Terminal Terminal = Terminal

instance Monad T1 where
  eta = Terminal
  mu = Terminal
