{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FinRel where

import Data.Type.Equality (TestEquality (..), type (:~:) (..))
import Data.Type.Nat (Nat (..), Nat0, Nat1, Nat2, Nat3, SNatI, snat, snatToNat)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (elem, repeat)

import Proarrow.Category.Instance.FinRel (Bitstring, FINREL (..), FinRel (..))

import Props
import Props.Hask ()
import Props.Mat ()
import Testable (Testable (..), TestableType (..), TestingEqShow (..), genSomeDef, invmap, pattern GenNonEmpty)

test :: TestTree
test =
  testGroup
    "FinRel"
    [ propCategory @FINREL
    , propTerminalObject @FINREL
    , propInitialObject @FINREL
    , propBinaryProducts_ @FINREL
    , propBinaryCoproducts_ @FINREL
    , propMonoidal_ @FINREL
    , propSymMonoidal_ @FINREL
    , propClosed_ @FINREL
    , propStarAutonomous_ @FINREL
    , testMonoid_ @(FR Nat0)
    , testMonoid_ @(FR Nat1)
    , testMonoid_ @(FR Nat2)
    , testMonoid_ @(FR Nat3)
    , testComonoid_ @(FR Nat0)
    , testComonoid_ @(FR Nat1)
    , testComonoid_ @(FR Nat2)
    , testComonoid_ @(FR Nat3)
    ]

instance Testable FINREL where
  showOb @(FR a) = show $ snatToNat $ snat @a
  eqOb @(FR a) @(FR b) = (\Refl -> Refl) <$> testEquality (snat @a) (snat @b)
  genSome = genSomeDef @'[FR Z, FR (S Z), FR (S (S Z)), FR (S (S (S Z)))]

instance (TestOb a, TestOb b) => TestableType (FinRel a b) where
  gen = invmap FinRel unFinRel gen
instance (TestOb a, TestOb b) => TestingEqShow (FinRel a b) where
  eqP (FinRel l) (FinRel r) = pure $ l == r
  showP (FinRel m) = show m

instance (SNatI n) => TestingEqShow (Bitstring n)
instance (SNatI n) => TestableType (Bitstring n) where
  gen = GenNonEmpty $ elem [minBound .. maxBound]
