{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FinRel where

import Data.Type.Equality (TestEquality (..), type (:~:) (..))
import Data.Type.Nat (Nat (..), Nat0, Nat1, Nat2, Nat3, SNatI, snat, snatToNat)
import Test.Falsify.Generator (Function (..), elem)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (elem, repeat)

import Proarrow.Category.Instance.FinRel (Bitstring, FINREL (..), FinRel (..))
import Proarrow.Core (type (~>))
import Proarrow.Profunctor.Instance.Identity (Id (..))

import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , invmap
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Props.Hask ()
import Props.Mat ()

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
    , propDistributive_ @FINREL
    , propClosed_ @FINREL
    , propStarAutonomous_ @FINREL
    , propCompactClosed_ @FINREL
    , propHypergraph_ @FINREL
    , testCommutativeMonoid_ @(FR Nat0)
    , testCommutativeMonoid_ @(FR Nat1)
    , testCommutativeMonoid_ @(FR Nat2)
    , testCommutativeMonoid_ @(FR Nat3)
    , -- morphism addition on a homset: a commutative monoid that is not Frobenius
      testCommutativeMonoid @(Id (FR Nat2) (FR Nat2)) (\r -> r)
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
instance TestableProfunctor FinRel

-- | A hom @a '~>' b@ wrapped as the identity profunctor 'Id' is a value of kind 'Type'; in a
-- biproduct category it is a commutative monoid under morphism addition. It is testable whenever
-- the underlying hom is.
instance (TestableType (a ~> b)) => TestableType (Id a b) where
  gen = invmap Id unId gen

instance (TestingEqShow (a ~> b)) => TestingEqShow (Id a b) where
  eqP (Id l) (Id r) = eqP l r
  showP (Id f) = showP f
instance Function (Id a b) where
  function = error "Function (Id a b): unused"

instance (SNatI n) => TestingEqShow (Bitstring n)
instance (SNatI n) => TestableType (Bitstring n) where
  gen = GenNonEmpty $ elem [minBound .. maxBound]
