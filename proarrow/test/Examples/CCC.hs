{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | Cartesian SMC terms: products alone, product exponentials independently of the target's
-- tensor, and case analysis with captured variables.
module Examples.CCC (test) where

import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.Nat (Nat (..), (:~>:) (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasProducts, PROD, type (&&))
import Proarrow.Testing (expect)
import Proarrow.Testing.Laws (testClosed)
import Proarrow.Tools.CCC (SYN (..), lift, toCCC, (**), type F)
import Proarrow.Tools.CCC qualified as CCC
import Props.Hask ()

-- These signatures check that compiling, lifting, copying and discarding do not require
-- exponentials or coproducts.
duplicate :: forall {k} (a :: k). (HasProducts k, Ob a) => a ~> (a && a)
duplicate = toCCC @(F a) @(F a :** F a) \x -> CCC.do
  y <- lift @(F a) @(F a) id x
  y ** y

{- HLINT ignore first "Use fst" -}
first :: forall {k} (a :: k) b. (HasProducts k, Ob a, Ob b) => (a && b) ~> a
first = toCCC @(F a :** F b) @(F a) \(a, _) -> a

-- Endofunctors have composition as their tensor. This arrow instead curries with respect
-- to their pointwise products, using Closed (PROD (Type -> Type)).
pairIdentities :: Nat Identity (Identity :~>: Product Identity Identity)
pairIdentities = CCC.curryPair @Identity @Identity

-- The outer variable is used at two binding depths.
captureTwice :: Bool -> Bool -> ((Bool, Bool), Bool)
captureTwice =
  toCCC @(F Bool) @(F Bool :-> ((F Bool :** F Bool) :** F Bool)) \x ->
    let f = CCC.lam (\y -> CCC.recast x ** y)
    in CCC.lam (\z -> (f CCC.! z) ** x)

test :: TestTree
test =
  testGroup
    "CCC"
    [ testClosed @(PROD Type) (\r -> r) (\r -> r)
    , testProperty "products, lifting and do binding" $ do
        mapM_ (\x -> expect ("duplicate " ++ show x) (x, x) (duplicate @Bool x)) ([False, True] :: [Bool])
        mapM_
          (\p@(x, _) -> expect ("first " ++ show p) x (first @Bool @Bool p))
          [(x, y) | x <- [False, True], y <- [False, True]]
    , testProperty "product swap" $
        expect "swap" (False, True) (CCC.swapProduct @Bool @Bool (True, False))
    , testProperty "application and currying" $ do
        expect "application" False (CCC.applyPair @Bool @Bool (not, True))
        expect "currying" (True, False) (CCC.curryPair @Bool @Bool True False)
    , testProperty "nested lambdas with a repeated argument" $
        mapM_
          (\(a, b) -> expect ("arguments " ++ show (a, b)) a (CCC.flipCurried3 @Bool @Bool @Bool (\x y z -> y && (x == z)) a b))
          [(a, b) | a <- [False, True], b <- [False, True]]
    , testProperty "a variable captured at two depths" $
        expect "capture" ((True, False), True) (captureTwice True False)
    , testProperty "injections and case analysis" $ do
        expect "right injection" (Right True) (CCC.injectRight @Bool @Bool True)
        expect "swap left" (Right True) (CCC.swapSum @Bool @Bool (Left True))
        expect "swap right" (Left False) (CCC.swapSum @Bool @Bool (Right False))
    , testProperty "case analysis shares the surrounding functions" $ do
        expect "left branch" False (CCC.caseEither @Bool @Bool @Bool (Left True, (not, id)))
        expect "right branch" True (CCC.caseEither @Bool @Bool @Bool (Right True, (not, id)))
    , testProperty "product exponentials in a category with composition tensor" $
        case unNat pairIdentities (Identity True) of
          Exp f -> expect "pointwise pair" (Pair (Identity True) (Identity False)) (f id (Identity False))
    ]
