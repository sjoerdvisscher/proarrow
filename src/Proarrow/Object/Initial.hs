module Proarrow.Object.Initial where

import Data.Kind (Type)
import Data.Void (Void, absurd)

import Proarrow.Core (CategoryOf(..), PRO)
import Proarrow.Object (Obj, obj)
import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Initial (InitialProfunctor)


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

instance (CategoryOf j, CategoryOf k) => HasInitialObject (PRO j k) where
  type InitialObject = InitialProfunctor
  initiate' Prof{} = Prof \case