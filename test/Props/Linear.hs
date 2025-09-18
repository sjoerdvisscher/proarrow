{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Linear where

import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.Linear (LINEAR (..), Linear (..), Top (..), With (..), mkWith, unsafeLinear)
import Proarrow.Core (CategoryOf (..), UN)

import Props
import Props.Hask (EnumAll (..))
import Testable (Testable (..), TestableProfunctor (..), genObDef, someElemWith)

test :: TestTree
test =
  testGroup
    "Linear"
    [ propCategory @LINEAR
    , propTerminalObject @LINEAR
    , propInitialObject @LINEAR
    , propBinaryProducts @LINEAR (\r -> r)
    , propBinaryCoproducts @LINEAR (\r -> r)
    , propMonoidal @LINEAR (\r -> r)
    ]

instance TestableProfunctor Linear where
  genP = someElemWith showP (Linear <$> enumAll)
  eqP (Linear l) (Linear r) = eqP (\a -> l a) (\a -> r a)
  showP (Linear f) = showP (\a -> f a)

instance Testable LINEAR where
  type TestOb a = (Ob a, TestOb (UN L a))
  showOb @(L a) = showOb @_ @a
  genOb = genObDef @'[L Bool, L (Bool, Bool), L (Maybe Bool)]

instance (Eq a, EnumAll a, EnumAll b) => EnumAll (a %1 -> b) where
  enumAll = go enumAll
    where
      go [] = []
      go (f : fs) = unsafeLinear f : go fs
instance (EnumAll a, EnumAll b) => EnumAll (With a b) where
  enumAll = [mkWith a b | a <- enumAll, b <- enumAll]
instance EnumAll Top where
  enumAll = [Top ()]
