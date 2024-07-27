module Proarrow.Object.Terminal where

import Data.Kind (Type)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..))
import Proarrow.Object (Obj, obj)
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))

class (CategoryOf k, Ob (TerminalObject :: k)) => HasTerminalObject k where
  type TerminalObject :: k
  terminate' :: Obj (a :: k) -> a ~> TerminalObject

terminate :: forall {k} a. (HasTerminalObject k, Ob (a :: k)) => a ~> TerminalObject
terminate = terminate' (obj @a)

type El a = TerminalObject ~> a

instance HasTerminalObject Type where
  type TerminalObject = ()
  terminate' _ _ = ()

instance (HasTerminalObject j, HasTerminalObject k) => HasTerminalObject (j, k) where
  type TerminalObject = '(TerminalObject, TerminalObject)
  terminate' (a1 :**: a2) = terminate' a1 :**: terminate' a2

instance (CategoryOf j, CategoryOf k) => HasTerminalObject (PRO j k) where
  type TerminalObject = TerminalProfunctor
  terminate' Prof{} = Prof \a -> TerminalProfunctor \\ a
