module Proarrow.Object.Initial where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude (type (~))

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Initial (InitialProfunctor)

class (CategoryOf k, Ob (InitialObject :: k)) => HasInitialObject k where
  type InitialObject :: k
  initiate :: (Ob (a :: k)) => InitialObject ~> a

initiate' :: forall {k} a' a. (HasInitialObject k) => (a' :: k) ~> a -> InitialObject ~> a
initiate' a = a . initiate @k @a' \\ a

instance HasInitialObject Type where
  type InitialObject = Void
  initiate = absurd

instance (HasInitialObject j, HasInitialObject k) => HasInitialObject (j, k) where
  type InitialObject = '(InitialObject, InitialObject)
  initiate = initiate :**: initiate

instance (CategoryOf j, CategoryOf k) => HasInitialObject (j +-> k) where
  type InitialObject = InitialProfunctor
  initiate = Prof \case {}

class (HasInitialObject k, HasTerminalObject k, (InitialObject :: k) ~ TerminalObject) => HasZeroObject k where
  zero :: (Ob (a :: k), Ob b) => a ~> b
instance (HasInitialObject k, HasTerminalObject k, (InitialObject :: k) ~ TerminalObject) => HasZeroObject k where
  zero = initiate . terminate
