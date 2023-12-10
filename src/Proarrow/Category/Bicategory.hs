{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf(..), CAT, Kind)
import Proarrow.Object (Obj, obj)
import Prelude (undefined)

infixr 5 :::
infixl 5 +++

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
  (\\\) :: ((BiOb kk j, BiOb kk k, Ob as, Ob bs) => r) -> (as :: Path kk j k) ~> bs -> r

obj1 :: forall {kk} {j} {k} (a :: kk j k). (Bicategory kk, BiOb kk j, BiOb kk k, Ob (a ::: Nil)) => Obj (a ::: Nil)
obj1 = obj @(a ::: Nil)

associator
  :: forall {kk} {h} {i} {j} {k} (a :: Path kk h i) (b :: Path kk i j) (c :: Path kk j k)
   . (Bicategory kk, Ob a, Ob b, Ob c)
  => (a +++ b) +++ c ~> a +++ (b +++ c)
associator = undefined

associatorInv
  :: forall {kk} {h} {i} {j} {k} (a :: Path kk h i) (b :: Path kk i j) (c :: Path kk j k)
   . (Bicategory kk, Ob a, Ob b, Ob c)
  => a +++ (b +++ c) ~> (a +++ b) +++ c
associatorInv = undefined

unitor
  :: forall {kk} {j} {k} (a :: Path kk j k)
   . (Bicategory kk, Ob a)
  => a +++ Nil ~> a
unitor = undefined

unitorInv
  :: forall {kk} {j} {k} (a :: Path kk j k)
   . (Bicategory kk, Ob a)
  => a ~> a +++ Nil
unitorInv = undefined

appendObj
  :: forall {kk} {i} {j} {k} (a :: Path kk i j) (b :: Path kk j k) r
   . (Ob a, Ob b)
  => (Ob (a +++ b) => r) -> r
appendObj _ = undefined