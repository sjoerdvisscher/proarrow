{-# LANGUAGE LinearTypes #-}

module TestFree where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Discrete (DISCRETE (..), Discrete (..))
import Proarrow.Category.Instance.Free (FREE (..), Free (..), UnitF, fold, type (**!))
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..), par)
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts, (&&&), type (*!))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Profunctor.Representable (Rep, Representable (..))
import Unsafe.Coerce (unsafeCoerce)

type data TestTy = IntTy' | StringTy'
type IntTy = D IntTy'
type StringTy = D StringTy'
data Test a b where
  Show :: Test IntTy StringTy
  Read :: Test StringTy IntTy
  Succ :: Test IntTy IntTy
  Dup :: Test StringTy StringTy

shw :: (i :: FREE cs Test) ~> EMB IntTy %1 -> i ~> EMB StringTy
shw = Emb Show

read :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB IntTy
read = Emb Read

succ :: (i :: FREE cs Test) ~> EMB IntTy %1 -> i ~> EMB IntTy
succ = Emb Succ

dup :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
dup = Emb Dup

test :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
test x = dup (shw (succ (read x)))

test2
  :: (HasBinaryProducts (FREE cs Test)) => (i :: FREE cs Test) ~> EMB StringTy -> i ~> (EMB StringTy *! EMB StringTy)
test2 x = x &&& test x

data family Interp :: DISCRETE TestTy +-> Type
instance FunctorForRep Interp where
  type Interp @ IntTy = P.Int
  type Interp @ StringTy = P.String
  fmap Refl = id

-- >>> testFold "123"
-- ("123","124124")
testFold :: P.String -> (P.String, P.String)
testFold = fold @'[HasBinaryProducts] @(Rep Interp) interp (test2 Id)
  where
    interp :: Test x y -> Rep Interp % x ~> Rep Interp % y
    interp Show = P.show
    interp Read = P.read
    interp Succ = P.succ
    interp Dup = (\s -> s P.++ s)

type SwapIn :: FC -> FC -> FC -> Constraint
class SwapIn (ia :: FC) i a | ia i -> a where
  swapIn :: (Ob a, Ob i) => a ** i ~> (ia :: FC)

instance SwapIn (a **! i) i a where
  swapIn = id
instance SwapIn (i **! a) i a where
  swapIn = swap
instance SwapIn i i UnitF where
  swapIn = leftUnitor

type Cls = '[Closed, Monoidal, SymMonoidal]
type FC = FREE Cls Test

lam
  :: forall ia i a b
   . (SwapIn ia i a, Ob i, Ob a)
  => ((i :: FC) ~> i %1 -> (ia :: FC) ~> b) %1 -> a ~> (i ~~> b)
lam = unsafeLinear \f -> curry (f id . swapIn)

($) :: forall {k} (a :: k) a' (b :: k) i. (Closed k, Ob b) => a ~> (i ~~> b) %1 -> a' ~> i %1 -> a ** a' ~> b
($) = unsafeLinear \f -> unsafeLinear \x -> apply @k @i @b . (f `par` x) \\ x

testLam :: forall (a :: FC) b. (Ob a, Ob b) => UnitF ~> ((a ~~> b) ~~> (a ~~> b))
testLam = lam \f -> lam \x -> f $ x

unsafeLinear :: (a -> b) -> (a %1 -> b)
unsafeLinear = unsafeCoerce
