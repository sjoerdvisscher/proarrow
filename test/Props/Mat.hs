{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Mat where

import Data.Type.Nat (Nat (..), snat, snatToNat)
import Data.Vec.Lazy (repeat)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (elem, repeat)

import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Core (UN)

import Props
import Testable (Testable (..), TestableType (..), TestingEqShow (..), genObDef, pattern GenNonEmpty)

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
    , testMonoid_ @(M Z :: MatK Int)
    , testMonoid_ @(M (S Z) :: MatK Int)
    , testMonoid_ @(M (S (S Z)) :: MatK Int)
    , testMonoid_ @(M (S (S (S Z))) :: MatK Int)
    , testComonoid_ @(M Z :: MatK Int)
    , testComonoid_ @(M (S Z) :: MatK Int)
    , testComonoid_ @(M (S (S Z)) :: MatK Int)
    , testComonoid_ @(M (S (S (S Z))) :: MatK Int)
    ]

instance Testable (MatK Int) where
  showOb @(M a) = show $ snatToNat $ snat @a
  genOb = genObDef @'[M Z, M (S Z), M (S (S Z)), M (S (S (S Z)))]

instance (TestOb (a :: MatK Int), TestOb b) => TestableType (Mat a b) where
  gen =
    GenNonEmpty $
      Mat <$> traverse (traverse \() -> liftA2 (*) (elem [1, -1]) (elem [0 .. 9])) (repeat @(UN M b) (repeat @(UN M a) ()))
instance (TestOb (a :: MatK Int), TestOb b) => TestingEqShow (Mat a b) where
  eqP (Mat l) (Mat r) = pure $ l == r
  showP (Mat m) = show m