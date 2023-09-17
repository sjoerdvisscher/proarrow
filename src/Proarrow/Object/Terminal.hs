module Proarrow.Object.Terminal where

import Data.Kind (Type)

import Proarrow.Core (CategoryOf, Category (..), type (~>))
import Proarrow.Object (Obj, obj)
import Proarrow.Category.Instance.Unit (Unit(..))

class (CategoryOf k, Ob (TerminalObject :: k)) => HasTerminalObject k where
  type TerminalObject :: k
  terminate' :: Obj (a :: k) -> a ~> TerminalObject

terminate :: forall {k} a. (HasTerminalObject k, Ob (a :: k)) => a ~> TerminalObject
terminate = terminate' (obj @a)

type El a = TerminalObject ~> a

instance HasTerminalObject Type where
  type TerminalObject = ()
  terminate' _ _ = ()

instance HasTerminalObject () where
  type TerminalObject = '()
  terminate' Unit = Unit
