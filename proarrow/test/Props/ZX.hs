{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.ZX where

import Data.Complex (Complex (..))
import Data.Map.Strict qualified as Map
import GHC.TypeNats (Nat)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (elem, id, repeat, (.))

import Proarrow.Category.Instance.ZX (ZX (..), enumAll, filterSparse, isZero, nat)
import Proarrow.Core (Promonad (..))
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , check
  , genNamed
  , genSomeDef
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws

test :: TestTree
test =
  testGroup
    "ZX calculus"
    [ testProperty "indexed composition agrees exactly with the entrywise join" $ do
        left <- genNamed @(ZX 2 3) "left"
        right <- genNamed @(ZX 1 2) "right"
        case (left, right) of
          (ZX n, ZX m) ->
            mapM_
              ( \entries ->
                  let expected =
                        filterSparse $
                          Map.fromListWith
                            (+)
                            [ ((c, a), mv * nv)
                            | ((c, b1), mv) <- Map.toList n
                            , ((b2, a), nv) <- Map.toList entries
                            , b1 == b2
                            ]
                  in case left . ZX entries of
                       ZX actual -> check "composition values or accumulation order changed" (actual == expected)
              )
              (m : [Map.filterWithKey (\(b, _) _ -> even (fromEnum b)) m])
    , testCategory @Nat
    , testDagger @Nat
    , testMonoidal_ @Nat
    , testHypergraph_ @Nat
    , testSymMonoidal_ @Nat
    , testClosed_ @Nat
    , testIsoMix_ @Nat
    , testCompactClosed_ @Nat
    , testTraced_ @Nat
    , testDialogue_ @Nat
    , testStarAutonomous_ @Nat
    , testCopyDiscard_ @Nat
    , testCommutativeMonoid_ @0
    , testCommutativeMonoid_ @1
    , testCommutativeMonoid_ @2
    , testCommutativeMonoid_ @3
    , testCocommutativeComonoid_ @0
    , testCocommutativeComonoid_ @1
    , testCocommutativeComonoid_ @2
    , testCocommutativeComonoid_ @3
    ]

instance Testable Nat where
  showOb @n = show $ nat @n
  genSome = genSomeDef @'[0, 1, 2]

instance (TestOb n, TestOb m) => TestableType (ZX n m) where
  gen = GenNonEmpty $ do
    let valGen = elem [-1, -sqrt 2, -0.5, 0, 0.5, sqrt 2, 1]
    let matrix = Map.fromList [((o, i), liftA2 (:+) valGen valGen) | o <- enumAll @m, i <- enumAll @n]
    ZX <$> sequenceA matrix
instance (TestOb n, TestOb m) => TestingEqShow (ZX n m) where
  eqP (ZX l) (ZX r) = pure $ all isZero (l Map.\\ r) && all isZero (r Map.\\ l) && all isZero (Map.intersectionWith (-) l r)
instance TestableProfunctor ZX
