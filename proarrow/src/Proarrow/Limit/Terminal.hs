{-# OPTIONS_GHC -Wno-orphans #-}

-- | Terminal objects: 'HasTerminalObject' with the unique arrow 'terminate', instances for the base
-- kinds, and global elements @'El' a = 'TerminalObject' '~>' a@.
module Proarrow.Limit.Terminal where

import Data.Kind (Constraint, Type)
import Prelude (Show, type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free
  ( Elem
  , Elems
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Lower
  , fromAll
  , withLowerOb
  )
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), UnitF)
import Proarrow.Core (CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), obj, type (+->))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Tools.Laws (Law (..), Laws (..), (===))

class (CategoryOf k, Ob (TerminalObject :: k)) => HasTerminalObject k where
  type TerminalObject :: k
  terminate :: (Ob (a :: k)) => a ~> TerminalObject

terminate' :: forall {k} a a'. (HasTerminalObject k) => (a :: k) ~> a' -> a ~> TerminalObject
terminate' a = terminate @k @a' . a \\ a

-- | The type of elements of `a`.
type El a = TerminalObject ~> a

-- | The constant arrow at an element: 'terminate', then the element.
const :: forall {k} (a :: k) b. (HasTerminalObject k, Ob a) => El b -> a ~> b
const u = u . terminate @k @a

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

-- | The right adjoint of the unique functor to the terminal category.
instance (HasTerminalObject k) => Representable (Corep (Constant '()) :: () +-> k) where
  type Corep (Constant '()) % a = TerminalObject
  index (Corep U.Unit) = terminate
  tabulate f = Corep U.Unit \\ f
  repMap U.Unit = id

-- | A monoidal category whose unit is terminal. The coherence maps are mutual
-- inverses; strict instances use identity defaults.
type Semicartesian :: Kind -> Constraint
class (HasTerminalObject k, Monoidal k) => Semicartesian k where
  unitToTerm :: (Unit :: k) ~> TerminalObject
  default unitToTerm :: ((Unit :: k) ~ TerminalObject) => (Unit :: k) ~> TerminalObject
  unitToTerm = id

  termToUnit :: (TerminalObject :: k) ~> Unit
  default termToUnit :: ((Unit :: k) ~ TerminalObject) => (TerminalObject :: k) ~> Unit
  termToUnit = id

instance Semicartesian ()
instance (Semicartesian j, Semicartesian k) => Semicartesian (j, k) where
  unitToTerm = unitToTerm :**: unitToTerm
  termToUnit = termToUnit :**: termToUnit

type SemicartesianStructures :: [Kind -> Constraint]
type SemicartesianStructures = '[Monoidal, HasTerminalObject, Semicartesian]

instance (SemicartesianStructures `Elems` cs) => HasStructure cs (p :: CAT k) Semicartesian where
  data Struct Semicartesian a b where
    TermToUnit :: Struct Semicartesian TermF UnitF
    UnitToTerm :: Struct Semicartesian UnitF TermF
  sameStructure TermToUnit TermToUnit = P.True
  sameStructure UnitToTerm UnitToTerm = P.True
  sameStructure _ _ = P.False
  foldStructure _ TermToUnit = P.pure termToUnit
  foldStructure _ UnitToTerm = P.pure unitToTerm

instance Show (Struct Semicartesian a b) where
  showsPrec _ TermToUnit = P.showString "termToUnit"
  showsPrec _ UnitToTerm = P.showString "unitToTerm"

instance (SemicartesianStructures `Elems` cs) => Semicartesian (FREE cs (p :: CAT k)) where
  termToUnit = St TermToUnit Nil
  unitToTerm = St UnitToTerm Nil

data family TermF :: k
instance (HasTerminalObject `Elem` cs) => IsFreeOb (TermF :: FREE cs p) where
  type Lower f TermF = TerminalObject
  withTypeableFreeOb r = r
  lowerOb @k' @_ r = fromAll @HasTerminalObject @cs @k' r
instance (HasTerminalObject `Elem` cs) => HasStructure cs (p :: CAT k) HasTerminalObject where
  data Struct HasTerminalObject a b where
    Terminate :: (Ob a) => Struct HasTerminalObject a TermF
  sameStructure Terminate Terminate = P.True
  foldStructure @f _ (Terminate @a) = P.pure P.$ withLowerOb @f @a terminate

instance Show (Struct HasTerminalObject a b) where
  showsPrec _ Terminate = P.showString "terminate"
instance (HasTerminalObject `Elem` cs) => HasTerminalObject (FREE cs (p :: CAT k)) where
  type TerminalObject = TermF
  terminate = St Terminate Nil

-- | Every arrow into the terminal object is 'terminate'.
instance Laws '[HasTerminalObject] where
  laws =
    [ Law "uniqueness" \ @a mor -> do
        g <- mor @a @TerminalObject "g"
        g === terminate
    ]
