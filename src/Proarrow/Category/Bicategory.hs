{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory (
  -- * Bicategories
  Bicategory(..)
  , BICAT
  , OkCategory
  , PathNilIsOb
  , id1
  , obj1
  , withAssoc
  , withUnital
  , appendObj

  -- * Paths
  , Path(..)
  , MKKIND
  , SPath(..)
  , IsPath(..)
  , withIsPath
  , type (+++)
  , append
  , isPathAppend
)
where

import Data.Kind (Constraint, Type)

import Proarrow.Core (CategoryOf(..), CAT, Kind, id, Any)
import Proarrow.Object (Obj, obj)

infixr 5 :::
infixl 5 +++

-- | The type of 2-parameter kind constructors.
type MKKIND = CAT Kind
type Path :: CAT k -> CAT k
-- | A type-level kind-threaded list. Used to strictify the bicategory and double category definitions.
-- @kk@ is a kind constructor, which creates a kind given two other kinds. (Each kind representing a 0-cell.)
type data Path kk j k where
  Nil :: Path kk k k
  (:::) :: kk i j -> Path kk j k -> Path kk i k

type family (+++) (ps :: Path kk a b) (qs :: Path kk b c) :: Path kk a c
type instance Nil +++ qs = qs
type instance (p ::: ps) +++ qs = p ::: (ps +++ qs)

class Ob @(Path kk j j) Nil => PathNilIsOb kk j
instance Ob @(Path kk j j) Nil => PathNilIsOb kk j
-- class (forall (p :: kk i j) (ps :: Path kk j k). (Ob1 kk p, Ob ps) => Ob' (p ::: ps)) => PathConsIsOb kk i j k
-- instance (forall (p :: kk i j) (ps :: Path kk j k). (Ob1 kk p, Ob ps) => Ob' (p ::: ps)) => PathConsIsOb kk i j k
class (CategoryOf (Path kk j k), forall (ps :: Path kk j k). Ob ps => IsPath ps) => OkCategory kk j k
instance (CategoryOf (Path kk j k), forall (ps :: Path kk j k). Ob ps => IsPath ps) => OkCategory kk j k

type BicategoryRequirements :: CAT k -> Constraint
class
  ( forall k. Ob0 kk k => PathNilIsOb kk k
  , forall j k. (Ob0 kk j, Ob0 kk k) => OkCategory kk j k
  -- , forall i j k. (Ob0 kk i, Ob0 kk j, Ob0 kk k) => PathConsIsOb kk i j k
  ) => BicategoryRequirements kk
instance
  ( forall k. Ob0 kk k => PathNilIsOb kk k
  , forall j k. (Ob0 kk j, Ob0 kk k) => OkCategory kk j k
  -- , forall i j k. (Ob0 kk i, Ob0 kk j, Ob0 kk k) => PathConsIsOb kk i j k
  ) => BicategoryRequirements kk

type BICAT kk = forall {j} {k}. CAT (Path kk j k)
-- | Bicategories. This is a strictified definition.
--
-- * 0-cells are kinds @i@, @j@, @k@... satisfying the @Ob0 kk@ constraint.
-- * 1-cells are types of kind @kk j k@ for any 0-cells @j@ and @k@, satisfying the @Ob1 kk@ constraint.
-- * 2-cells are values of type @ps ~> qs@, where @ps@ and @qs@ are of kind @Path kk j k@, representing lists of 1-cells.
type Bicategory :: CAT k -> Constraint
class BicategoryRequirements kk => Bicategory (kk :: CAT k) where
  type Ob0 kk (j :: k) :: Constraint
  type Ob0 kk j = Any j
  type Ob1 kk (p :: kk a b) :: Constraint
  type Ob1 kk p = Any p
  -- | Horizontal composition of 2-cells.
  o :: (ps :: Path kk i j) ~> qs -> rs ~> ss -> (ps +++ rs) ~> (qs +++ ss)
  -- | Observe constraints from a 2-cell value.
  (\\\) :: ((Ob0 kk i, Ob0 kk j, Ob ps, Ob qs) => r) -> (ps :: Path kk i j) ~> qs -> r
  -- fromList :: List (ps :: Path kk j k) qs -> ps ~> qs

-- | The identity 1-cell, the unit of horizontal composition
id1 :: (Bicategory kk, Ob0 kk k) => (Nil :: Path kk k k) ~> (Nil :: Path kk k k)
id1 = id

-- | @obj1 \@a@ is short for @obj \@(a ::: Nil)@
obj1 :: forall {kk} {j} {k} (a :: kk j k). (Bicategory kk, Ob0 kk j, Ob0 kk k, Ob (a ::: Nil)) => Obj (a ::: Nil)
obj1 = obj @(a ::: Nil)

withAssoc
  :: forall {kk} {h} {i} {j} {k} (a :: Path kk h i) (b :: Path kk i j) (c :: Path kk j k) r
   . (Bicategory kk, Ob0 kk h, Ob0 kk i, Ob a, Ob b, Ob c)
  => ((a +++ b) +++ c ~ a +++ (b +++ c) => r) -> r
withAssoc = go (singPath @a)
  where
    go :: forall a'. SPath a' -> ((a' +++ b) +++ c ~ a' +++ (b +++ c) => r) -> r
    go SNil r = r
    go (SCons a) r = go a r

withUnital
  :: forall {kk} {j} {k} (a :: Path kk j k) r
   . (Bicategory kk, Ob0 kk j, Ob0 kk k, Ob a)
  => (a +++ Nil ~ a => r) -> r
withUnital = go (singPath @a)
  where
    go :: forall a'. SPath a' -> (a' +++ Nil ~ a' => r) -> r
    go SNil r = r
    go (SCons a) r = go a r

appendObj
  :: forall {kk} {i} {j} {k} (a :: Path kk i j) (b :: Path kk j k) r
   . (Bicategory kk, Ob0 kk i, Ob0 kk j, Ob0 kk k, Ob a, Ob b)
  => (Ob (a +++ b) => r) -> r
appendObj r = r \\\ (obj @a `o` obj @b)



type IsPath :: forall {kk} {j} {k}. Path kk j k -> Constraint
class IsPath (ps :: Path kk j k) where
  singPath :: SPath ps
instance (Ob0 kk k) => IsPath (Nil :: Path kk k k) where
  singPath = SNil
instance (Ob0 kk j, Ob0 kk k, Ob1 kk p, IsPath ps) => IsPath ((p :: kk j k) ::: ps) where
  singPath = SCons singPath

type SPath :: Path kk j k -> Type
data SPath ps where
  SNil :: (Ob0 kk k) => SPath (Nil :: Path kk k k)
  SCons :: forall {kk} {j} {k} (p :: kk j k) ps. (Ob0 kk j, Ob0 kk k, Ob1 kk p) => SPath ps -> SPath (p ::: ps)

append :: SPath ps -> SPath qs -> SPath (ps +++ qs)
append SNil qs = qs
append (SCons ps) qs = SCons (append ps qs)

withIsPath :: SPath ps -> (IsPath ps => r) -> r
withIsPath SNil r = r
withIsPath (SCons ps) r = withIsPath ps r

isPathAppend :: forall {kk} {j} {k} (ps :: Path kk j k) qs r. (IsPath ps, IsPath qs) => (IsPath (ps +++ qs) => r) -> r
isPathAppend = withIsPath (append (singPath @ps) (singPath @qs))
