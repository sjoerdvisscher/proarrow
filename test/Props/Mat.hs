{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Mat where

import Data.Foldable (toList)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (repeat, elem)

import Proarrow.Category.Instance.Mat (Mat (..), MatK (..), Nat (..), Vec (..), repeat)
import Proarrow.Core (UN)

import Props
import Testable (Testable (..), TestableType (..), genObDef)

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
    , propClosed_ @(MatK Int)
    ]

instance Testable (MatK Int) where
  showOb @(M a) = show $ go (repeat @a ())
    where
      go :: Vec n () -> Int
      go Nil = 0
      go (Cons () n) = 1 + go n
  genOb = genObDef @'[M Z, M (S Z), M (S (S Z)), M (S (S (S Z)))]

instance (TestOb (a :: MatK Int), TestOb b) => TestableType (Mat a b) where
  gen = Just $ Mat <$> traverse (traverse \() -> liftA2 (*) (elem [1, -1]) (elem [0 .. 9])) (repeat @(UN M b) (repeat @(UN M a) ()))
  eqP (Mat l) (Mat r) = pure $ l == r
  showP (Mat m) = show (toList <$> toList m)