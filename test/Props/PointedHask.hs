{-# OPTIONS_GHC -Wno-orphans #-}

module Props.PointedHask where

import Data.List (intercalate)
import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.PointedHask (POINTED (..), Pointed (..), These (..))
import Proarrow.Core (CategoryOf (..), UN)

import Props
import Props.Hask (EnumAll (..))
import Testable (Testable (..), TestableProfunctor (..), genObDef)

test :: TestTree
test =
  testGroup
    "Pointed Hask"
    [ propCategory @POINTED
    , propTerminalObject @POINTED
    , propInitialObject @POINTED
    , propBinaryProducts @POINTED (\r -> r)
    , propBinaryCoproducts @POINTED (\r -> r)
    , propMonoidal @POINTED (\r -> r)
    ]

instance TestableProfunctor Pointed where
  genP = Pt <$> genP
  eqP (Pt l) (Pt r) = eqP l r
  showP (Pt f) = intercalate "," [show x ++ "->" ++ maybe "*" show (f x) | x <- enumAll]

instance Testable POINTED where
  type TestOb a = (Ob a, TestOb (UN P a))
  showOb @(P a) = showOb @_ @a
  genOb = genObDef @'[P Bool, P (Bool, Bool), P (Maybe Bool)]

instance (EnumAll a, EnumAll b) => EnumAll (These a b) where
  enumAll = (This <$> enumAll) ++ (That <$> enumAll) ++ (These <$> enumAll <*> enumAll)