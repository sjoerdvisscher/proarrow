{-# OPTIONS_GHC -Wno-orphans #-}

-- | Terminal objects: 'HasTerminalObject' with the unique arrow 'terminate', instances for the base
-- kinds, and global elements @'El' a = 'TerminalObject' '~>' a@.
module Proarrow.Limit.Terminal where

import Data.Kind (Type)
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
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Representable (..))

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

instance HasTerminalObject () where
  type TerminalObject = '()
  terminate = U.Unit

instance HasTerminalObject BOOL where
  type TerminalObject = TRU
  terminate @a = case obj @a of
    Fls -> F2T
    Tru -> Tru

instance (HasTerminalObject j, HasTerminalObject k) => HasTerminalObject (j, k) where
  type TerminalObject = '(TerminalObject, TerminalObject)
  terminate = terminate :**: terminate

instance (CategoryOf j, CategoryOf k) => HasTerminalObject (j +-> k) where
  type TerminalObject = TerminalProfunctor
  terminate = Prof \a -> TerminalProfunctor \\ a

instance (HasTerminalObject k, CategoryOf j) => Representable (TerminalProfunctor :: j +-> k) where
  type TerminalProfunctor % x = TerminalObject
  index TerminalProfunctor = terminate
  tabulate f = TerminalProfunctor \\ f
  repMap _ = id

class ((Unit :: k) ~ TerminalObject, HasTerminalObject k, Monoidal k) => Semicartesian k
instance ((Unit :: k) ~ TerminalObject, HasTerminalObject k, Monoidal k) => Semicartesian k

data family TermF :: k
instance (HasTerminalObject `Elem` cs) => IsFreeOb (TermF :: FREE cs p) where
  type Lower f TermF = TerminalObject
  lowerOb @k' @_ r = fromAll @HasTerminalObject @cs @k' r
instance (HasTerminalObject `Elem` cs) => HasStructure cs (p :: CAT k) HasTerminalObject where
  data Struct HasTerminalObject a b where
    Terminate :: (Ob a) => Struct HasTerminalObject a TermF
  foldStructure @f _ (Terminate @a) = withLowerOb @f @a terminate
instance Show (Struct HasTerminalObject a b) where
  showsPrec _ Terminate = P.showString "terminate"
instance (HasTerminalObject `Elem` cs) => HasTerminalObject (FREE cs (p :: CAT k)) where
  type TerminalObject = TermF
  terminate = St Terminate Nil
