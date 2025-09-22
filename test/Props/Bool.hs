{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Bool where

import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Core (obj)

import Props
import Testable (Testable (..), genObDef, TestableType (..), optGen)

test :: TestTree
test =
  testGroup
    "Booleans"
    [ propCategory @BOOL
    , propTerminalObject @BOOL
    , propInitialObject @BOOL
    , propBinaryProducts_ @BOOL
    , propBinaryCoproducts_ @BOOL
    , propClosed_ @BOOL
    ]

instance Testable BOOL where
  showOb @a = case obj @a of
    Fls -> "FLS"
    Tru -> "TRU"
  genOb = genObDef @'[FLS, TRU]

instance (TestOb a, TestOb b) => TestableType (Booleans a b) where
  gen = optGen $ case (obj @a, obj @b) of
    (Fls, Fls) -> [Fls]
    (Fls, Tru) -> [F2T]
    (Tru, Tru) -> [Tru]
    (Tru, Fls) -> []
  eqP _ _ = pure True
  showP Fls = "F->F"
  showP F2T = "F->T"
  showP Tru = "T->T"