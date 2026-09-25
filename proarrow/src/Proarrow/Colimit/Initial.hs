{-# OPTIONS_GHC -Wno-orphans #-}

-- | Initial objects: 'HasInitialObject' with the unique arrow 'initiate', instances for the base kinds,
-- and 'HasZeroObject' for categories where the initial and terminal objects coincide.
module Proarrow.Colimit.Initial where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude (Show, type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free
  ( Elem (..)
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Lower
  , withLowerOb
  )
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Tools.Laws (Law (..), Laws (..), (=:=))

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

instance HasInitialObject BOOL where
  type InitialObject = FLS
  initiate @a = case obj @a of
    Fls -> Fls
    Tru -> F2T

instance (HasInitialObject j, HasInitialObject k) => HasInitialObject (j, k) where
  type InitialObject = '(InitialObject, InitialObject)
  initiate = initiate :**: initiate

instance (CategoryOf j, CategoryOf k) => HasInitialObject (j +-> k) where
  type InitialObject = InitialProfunctor
  initiate = Prof \case {}

instance (HasInitialObject j, CategoryOf k) => Corepresentable (TerminalProfunctor :: j +-> k) where
  type TerminalProfunctor %% x = InitialObject
  coindex TerminalProfunctor = initiate
  cotabulate f = TerminalProfunctor \\ f
  corepMap _ = id

class (HasInitialObject k, HasTerminalObject k, (InitialObject :: k) ~ TerminalObject) => HasZeroObject k where
  zero :: (Ob (a :: k), Ob b) => a ~> b
instance (HasInitialObject k, HasTerminalObject k, (InitialObject :: k) ~ TerminalObject) => HasZeroObject k where
  zero = initiate . terminate

data family InitF :: k
instance (HasInitialObject `Elem` cs) => IsFreeOb (InitF :: FREE cs p) where
  type Lower f InitF = InitialObject
  lowerOb @k' @_ r = fromAll @HasInitialObject @cs @k' r
instance (HasInitialObject `Elem` cs) => HasStructure cs (p :: CAT k) HasInitialObject where
  data Struct HasInitialObject a b where
    Initial :: (Ob b) => Struct HasInitialObject InitF b
  foldStructure @f _ (Initial @b) = withLowerOb @f @b initiate
instance Show (Struct HasInitialObject a b) where
  showsPrec _ Initial = P.showString "initiate"
instance (HasInitialObject `Elem` cs) => HasInitialObject (FREE cs (p :: CAT k)) where
  type InitialObject = InitF
  initiate = St Initial Nil

instance (HasInitialObject k) => HasTerminalObject (OPPOSITE k) where
  type TerminalObject = OP InitialObject
  terminate = Op initiate

instance (HasTerminalObject k) => HasInitialObject (OPPOSITE k) where
  type InitialObject = OP TerminalObject
  initiate = Op terminate

-- | Every arrow out of the initial object is 'initiate'.
instance Laws '[HasInitialObject] where
  laws =
    [ Law "uniqueness" \ @a gen -> do
        g <- gen @InitialObject @a "g"
        g =:= initiate
    ]
