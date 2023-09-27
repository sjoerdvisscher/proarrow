module Proarrow.Object.Initial where

import Data.Kind (Type)
import Data.Void (Void, absurd)

import Proarrow.Core (CategoryOf, Category (..), type (~>))
import Proarrow.Object (Obj, obj)
import Proarrow.Category.Instance.Product ((:**:)(..))

class (CategoryOf k, Ob (InitialObject :: k)) => HasInitialObject k where
  type InitialObject :: k
  initiate' :: Obj (a :: k) -> InitialObject ~> a

initiate :: forall {k} a. (HasInitialObject k, Ob (a :: k)) => InitialObject ~> a
initiate = initiate' (obj @a)

instance HasInitialObject Type where
  type InitialObject = Void
  initiate' _ = absurd

instance (HasInitialObject j, HasInitialObject k) => HasInitialObject (j, k) where
  type InitialObject = '(InitialObject, InitialObject)
  initiate' (a1 :**: a2) = initiate' a1 :**: initiate' a2