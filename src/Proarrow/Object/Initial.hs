{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Object.Initial where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude (Eq, Show, type (~))

import Proarrow.Category.Instance.Free (Elem, FREE (..), Free (..), HasStructure (..), IsFreeOb (..), Ok)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
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

instance HasInitialObject () where
  type InitialObject = '()
  initiate = Unit

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

data family InitF :: k
instance (HasInitialObject `Elem` cs) => IsFreeOb (InitF :: FREE cs p) where
  type Lower f InitF = InitialObject
  withLowerOb r = r
instance (HasInitialObject `Elem` cs) => HasStructure cs p HasInitialObject where
  data Struct HasInitialObject a b where
    Initial :: (Ob b) => Struct HasInitialObject InitF b
  foldStructure @f _ (Initial @b) = withLowerOb @b @f initiate
deriving instance Eq (Struct HasInitialObject a b)
deriving instance Show (Struct HasInitialObject a b)
instance (Ok cs p, HasInitialObject `Elem` cs) => HasInitialObject (FREE cs p) where
  type InitialObject = InitF
  initiate = Str Initial Id

instance (HasInitialObject k) => HasTerminalObject (OPPOSITE k) where
  type TerminalObject = OP InitialObject
  terminate = Op initiate

instance (HasTerminalObject k) => HasInitialObject (OPPOSITE k) where
  type InitialObject = OP TerminalObject
  initiate = Op terminate
