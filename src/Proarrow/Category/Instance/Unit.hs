module Proarrow.Category.Instance.Unit where

import Proarrow.Core (CAT, CategoryOf(..), Profunctor(..), Promonad(..), dimapDefault)
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))


type data UNIT = U

type Unit :: CAT UNIT
data Unit a b where
  Unit :: Unit U U


-- | The category with one object, the terminal category.
instance CategoryOf UNIT where
  type (~>) = Unit
  type Ob a = a ~ U

instance Promonad Unit where
  id = Unit
  Unit . Unit = Unit

instance Profunctor Unit where
  dimap = dimapDefault
  r \\ Unit = r

instance HasTerminalObject UNIT where
  type TerminalObject = U
  terminate' Unit = Unit

instance HasInitialObject UNIT where
  type InitialObject = U
  initiate' Unit = Unit
