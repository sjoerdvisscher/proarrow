{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))
import Fcf.Core (Exp, Eval)
import Prelude (undefined)

import Proarrow.Core (CategoryOf(..), CAT, Kind)
import Proarrow.Object (Obj, obj)

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

data MapFunc :: MKKIND -> MKKIND -> Type
type family Eval' (f :: MapFunc kk jj -> Type) (p :: kk a b) :: jj a b
data MapPath :: (MapFunc kk jj -> Type) -> Path kk a b -> Exp (Path jj a b)
type instance Eval (MapPath f Nil) = Nil
type instance Eval (MapPath f (p ::: ps)) = Eval' f p ::: Eval (MapPath f ps)

type family (+++) (ps :: Path kk a b) (qs :: Path kk b c) :: Path kk a c
type instance Nil +++ qs = qs
type instance (p ::: ps) +++ qs = p ::: (ps +++ qs)

class Ob (Eval (MapPath f ps)) => ObMap f ps
instance Ob (Eval (MapPath f ps)) => ObMap f ps

type AppendTypes ps qs f =
  ( Eval (MapPath f ps) +++ Eval (MapPath f qs) ~ Eval (MapPath f (ps +++ qs))
  , IsPath (ps +++ qs) f
  )

type IsPath :: forall {kk} {jj} {j} {k}. Path kk j k -> (MapFunc kk jj -> Type) -> Constraint
class (Ob ps => ObMap f ps) => IsPath (ps :: Path kk j k) (f :: MapFunc kk jj -> Type) where
  withAppendIsPath' :: IsPath qs f => proxy qs -> (AppendTypes ps qs f => r) -> r
instance Ob (Nil :: Path jj j j) => IsPath (Nil :: Path kk j j) (f :: MapFunc kk jj -> Type) where
  withAppendIsPath' _ r = r
-- instance (Ob1 kk p, IsPath ps f, Ob (Eval' f p ::: Eval (MapPath f ps))) => IsPath (p ::: ps) f where
--   withAppendIsPath' = withAppendIsPath' @ps @f

withAppendIsPath :: forall ps qs f r. (IsPath ps f, IsPath qs f) =>
  ((Eval (MapPath f ps) +++ Eval (MapPath f qs) ~ Eval (MapPath f (ps +++ qs)), IsPath (ps +++ qs) f) => r) -> r
withAppendIsPath = withAppendIsPath' @ps @f (Proxy @qs)

class Ob @(Path kk j j) Nil => PathNilIsOb kk j
instance Ob @(Path kk j j) Nil => PathNilIsOb kk j

type BICAT kk = forall {j} {k}. CAT (Path kk j k)
-- | Bicategories. This is a strictified definition.
class (forall j k. (Ob0 kk j, Ob0 kk k) => CategoryOf (Path kk j k), forall j. Ob0 kk j => PathNilIsOb kk j) => Bicategory kk where
  type Ob0 kk k :: Constraint
  type Ob1 kk (p :: kk a b) :: Constraint
  -- | Horizontal composition
  o :: (as :: Path kk j k) ~> bs -> cs ~> ds -> (as +++ cs) ~> (bs +++ ds)
  (\\\) :: ((Ob0 kk j, Ob0 kk k, Ob as, Ob bs) => r) -> (as :: Path kk j k) ~> bs -> r

-- | `obj1 @a` is short for `obj @(a ::: Nil)`
obj1 :: forall {kk} {j} {k} (a :: kk j k). (Bicategory kk, Ob0 kk j, Ob0 kk k, Ob (a ::: Nil)) => Obj (a ::: Nil)
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