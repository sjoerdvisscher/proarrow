module Proarrow.Object.Initial where

import Data.Kind (Type)
import Data.Void (Void, absurd)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..))
import Proarrow.Object (obj)
import Proarrow.Profunctor.Initial (InitialProfunctor)

class (CategoryOf k, Ob (InitialObject :: k)) => HasInitialObject k where
  {-# MINIMAL initiate | initiate' #-}
  type InitialObject :: k
  initiate :: (Ob (a :: k)) => InitialObject ~> a
  initiate @a = initiate' (obj @a)
  initiate' :: (a' :: k) ~> a -> InitialObject ~> a
  initiate' @a' a = a . initiate @k @a' \\ a

instance HasInitialObject Type where
  type InitialObject = Void
  initiate = absurd

instance (HasInitialObject j, HasInitialObject k) => HasInitialObject (j, k) where
  type InitialObject = '(InitialObject, InitialObject)
  initiate = initiate :**: initiate

instance (CategoryOf j, CategoryOf k) => HasInitialObject (PRO j k) where
  type InitialObject = InitialProfunctor
  initiate = Prof \case {}
