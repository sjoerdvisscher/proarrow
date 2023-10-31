{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf(..), CAT, Kind)


-- | The type of kind constructors.
type MKKIND = Kind -> Kind -> Kind
type Path :: MKKIND -> MKKIND
-- | A type-level kind-threaded list. Used to strictify the bicategory and double category definitions.
-- @kk@ is a kind constructor, which creates a kind given two other kinds. (Each kind representing a category.)
data Path kk a b where
  Nil :: Path kk a a
  (:::) :: kk a b -> Path kk b c -> Path kk a c

type family (+++) (ps :: Path kk a b) (qs :: Path kk b c) :: Path kk a c
type instance Nil +++ qs = qs
type instance (p ::: ps) +++ qs = p ::: (ps +++ qs)


class Ob @(Path kk j j) Nil => PathNilIsOb kk j
instance Ob @(Path kk j j) Nil => PathNilIsOb kk j

type BICAT kk = forall {j} {k}. CAT (Path kk j k)
-- | Bicategories. This is a strictified definition.
class (forall j k. (BiOb kk j, BiOb kk k) => CategoryOf (Path kk j k), forall j. BiOb kk j => PathNilIsOb kk j) => Bicategory kk where
  type BiOb kk k :: Constraint
  -- | Horizontal composition
  o :: (as :: Path kk j k) ~> bs -> cs ~> ds -> (as +++ cs) ~> (bs +++ ds)
  (\\\) :: ((BiOb kk j, BiOb kk k) => r) -> (as :: Path kk j k) ~> bs -> r
