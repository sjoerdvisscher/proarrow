{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.ZX where

import Data.Complex (Complex (..))
import Data.Map.Strict qualified as Map
import GHC.TypeNats (Nat)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (elem, repeat)

import Proarrow.Category.Instance.ZX (ZX (..), enumAll, isZero, nat)
import Props
import Testable (Testable (..), TestableType (..), TestingEqShow (..), genSomeDef, pattern GenNonEmpty)

test :: TestTree
test =
  testGroup
    "ZX calculus"
    [ propCategory @Nat
    , propTerminalObject @Nat
    , propInitialObject @Nat
    , propMonoidal_ @Nat
    , propSymMonoidal_ @Nat
    , propClosed_ @Nat
    , testMonoid_ @0
    , testMonoid_ @1
    , testMonoid_ @2
    , testMonoid_ @3
    , testComonoid_ @0
    , testComonoid_ @1
    , testComonoid_ @2
    , testComonoid_ @3
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
