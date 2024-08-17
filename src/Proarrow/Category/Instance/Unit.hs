{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Unit where

import Prelude (type (~))

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))

type Unit :: CAT ()
data Unit a b where
  Unit :: Unit '() '()

-- | The category with one object, the terminal category.
instance CategoryOf () where
  type (~>) = Unit
  type Ob a = a ~ '()

instance Promonad Unit where
  id = Unit
  Unit . Unit = Unit

instance Profunctor Unit where
  dimap = dimapDefault
  r \\ Unit = r

instance HasTerminalObject () where
  type TerminalObject = '()
  terminate' Unit = Unit

instance HasInitialObject () where
  type InitialObject = '()
  initiate' Unit = Unit
