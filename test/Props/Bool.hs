{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Bool where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (discard)
import Prelude

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Core (obj)

import Props
import Testable (Testable (..), TestableProfunctor (..), genObDef)

test :: TestTree
test =
  testGroup
    "Booleans"
    [ propCategory @BOOL
    , propTerminalObject @BOOL
    , propInitialObject @BOOL
    , propBinaryProducts_ @BOOL
    , propBinaryCoproducts_ @BOOL
    ]

instance Testable BOOL where
  showOb @a = case obj @a of
    Fls -> "FLS"
    Tru -> "TRU"
  genOb = genObDef @'[FLS, TRU]

instance TestableProfunctor Booleans where
  genP @a @b = case (obj @a, obj @b) of
    (Fls, Fls) -> pure Fls
    (Fls, Tru) -> pure F2T
    (Tru, Tru) -> pure Tru
    (Tru, Fls) -> discard
  eqP _ _ = pure True
  showP Fls = "F->F"
  showP F2T = "F->T"
  showP Tru = "T->T"
