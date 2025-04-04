module Proarrow.Object.Terminal where

import Data.Kind (Type)
import Prelude (type (~))

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Terminal (TerminalProfunctor (..))

class (CategoryOf k, Ob (TerminalObject :: k)) => HasTerminalObject k where
  type TerminalObject :: k
  terminate :: (Ob (a :: k)) => a ~> TerminalObject

terminate' :: forall {k} a a'. (HasTerminalObject k) => (a :: k) ~> a' -> a ~> TerminalObject
terminate' a = terminate @k @a' . a \\ a

-- | The type of elements of `a`.
type El a = TerminalObject ~> a

instance HasTerminalObject Type where
  type TerminalObject = ()
  terminate _ = ()

instance (HasTerminalObject j, HasTerminalObject k) => HasTerminalObject (j, k) where
  type TerminalObject = '(TerminalObject, TerminalObject)
  terminate = terminate :**: terminate

instance (CategoryOf j, CategoryOf k) => HasTerminalObject (j +-> k) where
  type TerminalObject = TerminalProfunctor
  terminate = Prof \a -> TerminalProfunctor \\ a

class ((Unit :: k) ~ TerminalObject, HasTerminalObject k, Monoidal k) => Semicartesian k
instance ((Unit :: k) ~ TerminalObject, HasTerminalObject k, Monoidal k) => Semicartesian k