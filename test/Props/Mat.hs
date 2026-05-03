{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Mat where

import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), type (:~:) (..))
import Data.Type.Nat (Nat (..), snat, snatToNat, SNat (..), Nat0, Nat1, Nat2, Nat3, SNatI)
import Data.Vec.Lazy (repeat, Vec (..))
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (elem, repeat)

import Proarrow.Category.Instance.Mat (Mat (..), MatK (..), App)
import Proarrow.Core (type (+->))
import Proarrow.Profunctor.Representable (Rep)

import Props
import Props.Hask ()
import Testable (Testable (..), TestableType (..), TestingEqShow (..), genSomeDef, pattern GenNonEmpty, invmap, GenTotal (..), one)

test :: TestTree
test =
  testGroup
    "Matrix"
    [ propCategory @(MatK Int)
    , propTerminalObject @(MatK Int)
    , propInitialObject @(MatK Int)
    , propBinaryProducts_ @(MatK Int)
    , propBinaryCoproducts_ @(MatK Int)
    , propMonoidal_ @(MatK Int)
    , propSymMonoidal_ @(MatK Int)
    , propClosed_ @(MatK Int)
    , propStarAutonomous_ @(MatK Int)
    , testMonoid_ @(M Nat0 :: MatK Int)
    , testMonoid_ @(M Nat1 :: MatK Int)
    , testMonoid_ @(M Nat2 :: MatK Int)
    , testMonoid_ @(M Nat3 :: MatK Int)
    , testComonoid_ @(M Nat0 :: MatK Int)
    , testComonoid_ @(M Nat1 :: MatK Int)
    , testComonoid_ @(M Nat2 :: MatK Int)
    , testComonoid_ @(M Nat3 :: MatK Int)
    , testProperty "App functor" $ propProfunctor @(Rep App :: MatK Int +-> Type)
    ]

instance Testable (MatK Int) where
  showOb @(M a) = show $ snatToNat $ snat @a
  eqOb @(M a) @(M b) = (\Refl -> Refl) <$> testEquality (snat @a) (snat @b)
  genSome = genSomeDef @'[M Z, M (S Z), M (S (S Z)), M (S (S (S Z)))]

instance (TestOb (a :: MatK Int), TestOb b) => TestableType (Mat a b) where
  gen = invmap Mat unMat gen
instance (TestOb (a :: MatK Int), TestOb b) => TestingEqShow (Mat a b) where
  eqP (Mat l) (Mat r) = pure $ l == r
  showP (Mat m) = show m

instance (Eq a, Show a) => TestingEqShow (Vec n a)
instance (Eq a, Show a, TestableType a, SNatI n) => TestableType (Vec n a) where
  gen = case gen of
    GenEmpty absurd -> case snat @n of
      SZ -> one VNil
      SS -> GenEmpty \(a ::: _) -> absurd a
    GenNonEmpty g -> GenNonEmpty $ sequence (repeat @n g)

instance TestingEqShow Int
instance TestableType Int where
  gen = GenNonEmpty $ liftA2 (*) (elem [1, -1]) (elem [0 .. 9])
