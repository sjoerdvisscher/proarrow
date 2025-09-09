{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Mat where

import Data.Foldable (toList)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (repeat)

import Proarrow.Category.Instance.Mat (Mat (..), MatK (..), Nat (..), Vec (..), repeat)
import Proarrow.Core (CAT)

import Props
import Testable (Testable (..), TestableProfunctor (..), genObDef, someElem)

test :: TestTree
test =
  testGroup
    "Matrix"
    [ propCategory @(MatK Int)
    , propTerminalObject @(MatK Int)
    , propInitialObject @(MatK Int)
    , propBinaryProducts_ @(MatK Int)
    , propBinaryCoproducts_ @(MatK Int)
    ]

instance Testable (MatK Int) where
  showOb @(M a) = show $ go (repeat @a ())
    where
      go :: Vec n () -> Int
      go Nil = 0
      go (Cons () n) = 1 + go n
  genOb = genObDef @'[M Z, M (S Z), M (S (S Z)), M (S (S (S Z))), M (S (S (S (S Z))))]

instance TestableProfunctor (Mat :: CAT (MatK Int)) where
  genP @(M a) @(M b) = Mat <$> traverse (traverse \() -> liftA2 (*) (someElem [1, -1]) (someElem [0 .. 9])) (repeat @b (repeat @a ()))
  eqP (Mat l) (Mat r) = pure $ l == r
  showP (Mat m) = show (toList <$> toList m)