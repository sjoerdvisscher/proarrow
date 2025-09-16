{-# OPTIONS_GHC -Wno-orphans #-}

module Props.ZX where

import Data.Complex (Complex (..))
import Data.Map.Strict qualified as Map
import GHC.TypeNats (Nat)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (repeat)

import Proarrow.Category.Instance.ZX (ZX (..), enumAll, isZero, nat)
import Props
import Testable (Testable (..), TestableProfunctor (..), genObDef, someElem)

test :: TestTree
test =
  testGroup
    "ZX calculus"
    [ propCategory @Nat
    , propTerminalObject @Nat
    , propInitialObject @Nat
    ]

instance Testable Nat where
  showOb @n = show $ nat @n
  genOb = genObDef @'[0, 1, 2, 3]

values :: [Double]
values = [-1, -sqrt 2, -0.5, 0, 0.5, sqrt 2, 1]

instance TestableProfunctor ZX where
  genP @n @m = do
    let matrix = Map.fromList [((o, i), liftA2 (:+) (someElem values) (someElem values)) | o <- enumAll @m, i <- enumAll @n]
    ZX <$> sequenceA matrix
  eqP (ZX l) (ZX r) = pure $ all isZero (l Map.\\ r) && all isZero (r Map.\\ l) && all isZero (Map.intersectionWith (-) l r)
  showP = show