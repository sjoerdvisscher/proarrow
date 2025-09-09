{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Hask where

import Control.Monad (replicateM)
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Void (Void)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude

import Props
import Testable (Testable (..), TestableProfunctor (..), genObDef, someElem, someElemWith)

test :: TestTree
test =
  testGroup
    "Hask"
    [ propCategory @Type
    , propTerminalObject @Type
    , propInitialObject @Type
    , propBinaryProducts @Type (\r -> r)
    , propBinaryCoproducts @Type (\r -> r)
    ]

instance Testable Type where
  type TestOb (a :: Type) = (Typeable a, Eq a, Show a, EnumAll a)
  showOb @a = show (typeRep @a)
  genOb = genObDef @'[Bool, (Bool, Bool), Maybe Bool]

class EnumAll a where
  enumAll :: [a]
instance EnumAll Void where
  enumAll = []
instance EnumAll () where
  enumAll = [()]
instance EnumAll Bool where
  enumAll = [False, True]
instance (EnumAll a, EnumAll b) => EnumAll (a, b) where
  enumAll = [(a, b) | a <- enumAll, b <- enumAll]
instance (EnumAll a, EnumAll b) => EnumAll (Either a b) where
  enumAll = [Left a | a <- enumAll] ++ [Right b | b <- enumAll]
instance (EnumAll a) => EnumAll (Maybe a) where
  enumAll = Nothing : map Just enumAll
instance (Eq a, EnumAll a, EnumAll b) => EnumAll (a -> b) where
  enumAll = do
    let as = enumAll
    table <- zip as <$> replicateM (length as) enumAll
    return \a -> case lookup a table of
      Just b -> b
      Nothing -> error "enumAll @(a -> b): value of type a passed that is not in enumAll @a"
instance TestableProfunctor (->) where
  genP = someElemWith showP enumAll
  eqP l r = do
    let as = enumAll
    if length as == 0
      then pure True -- Shortcut, otherwise all tests are discarded
      else do
        a <- someElem as
        pure $ l a == r a
  showP f = intercalate "," [show x ++ "->" ++ show (f x) | x <- enumAll]