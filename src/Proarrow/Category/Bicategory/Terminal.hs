{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Terminal where

import Proarrow.Category.Bicategory (Bicategory(..), Monad (..))
import Proarrow.Core (CategoryOf(..), Profunctor(..), CAT, Promonad (..), dimapDefault)
import Data.Type.Equality (type (~~))

data TK = T0
type TERMK :: CAT TK
data TERMK j k where
  T1 :: TERMK T0 T0

type Terminal :: CAT (TERMK j k)
data Terminal a b where
  Terminal :: Terminal T1 T1

instance Profunctor (Terminal :: CAT (TERMK T0 T0)) where
  dimap = dimapDefault
  r \\ Terminal = r
instance Promonad (Terminal :: CAT (TERMK T0 T0)) where
  id = Terminal
  Terminal . Terminal = Terminal
instance (j ~ T0, k ~ T0) => CategoryOf (TERMK j k) where
  type (~>) = Terminal
  type Ob @(TERMK j k) p = (p ~~ T1)

instance Bicategory TERMK where
  type Ob0 TERMK k = (k ~ T0)
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