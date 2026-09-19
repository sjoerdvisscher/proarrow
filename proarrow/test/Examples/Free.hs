{- HLINT ignore "Redundant $" -}
{-# LANGUAGE LinearTypes #-}

-- | A small free category on a two-object quiver, folded through an interpretation, plus a lambda
-- term built in the free cartesian closed category. Most of this is checked by compiling it -- the
-- types are the point -- but the fold does produce a value, so that much is asserted at the end.
module Examples.Free where

import Data.Kind (Constraint, Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Finite (..), Indexed (..))
import Proarrow.Category.Instance.Discrete (DISCRETE (..), Discrete (..))
import Proarrow.Category.Instance.Free (FREE (..), Free (..), fold)
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..), UnitF, (**), type (**!))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts, (&&&), type (*!))
import Proarrow.Profunctor.Representable (Rep, Representable (..))
import Proarrow.Testing (expect)
import Unsafe.Coerce (unsafeCoerce)

type data TestTy = IntTy' | StringTy'

instance Indexed TestTy
instance Finite TestTy where type Objects TestTy = '[IntTy', StringTy']

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

pipeline :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
pipeline x = dup (shw (succ (read x)))

pipelineWithInput
  :: (HasBinaryProducts (FREE cs Test)) => (i :: FREE cs Test) ~> EMB StringTy -> i ~> (EMB StringTy *! EMB StringTy)
pipelineWithInput x = x &&& pipeline x

data family Interp :: DISCRETE TestTy +-> Type
instance FunctorForRep Interp where
  type Interp @ IntTy = P.Int
  type Interp @ StringTy = P.String
  fmap Refl = id

-- | Read the string as an int, increment, show it, and duplicate -- alongside the untouched input.
testFold :: P.String -> (P.String, P.String)
testFold = fold @'[HasBinaryProducts] @(Rep Interp) interp (pipelineWithInput Nil)
  where
    interp :: Test x y -> Rep Interp % x ~> Rep Interp % y
    interp Show = P.show
    interp Read = P.read
    interp Succ = P.succ
    interp Dup = \s -> s P.++ s

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
($) = unsafeLinear \f -> unsafeLinear \x -> apply @k @i @b . (f ** x) \\ x

testLam :: forall (a :: FC) b. (Ob a, Ob b) => UnitF ~> ((a ~~> b) ~~> (a ~~> b))
testLam = lam \f -> lam \x -> f $ x

unsafeLinear :: (a -> b) -> (a %1 -> b)
unsafeLinear = unsafeCoerce

test :: TestTree
test =
  testGroup
    "Free"
    [ testProperty
        "the pipeline folds through the interpretation"
        (expect "input paired with succ-then-duplicate" ("123", "124124") (testFold "123"))
    ]
