{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.PointedHask where

import Data.List (intercalate)
import Data.Void (Void)
import Test.Falsify.Generator (Function, oneof)
import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.PointedHask (POINTED (..), Pointed (..), These (..))
import Proarrow.Core (CategoryOf (..), UN)

import Props
import Props.Hask ()
import Testable (EnumAll (..), GenTotal (..), Testable (..), TestableType (..), genObDef, invmap)

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
    , propSymMonoidal @POINTED (\r -> r)
    , propMonoid @(P Void) (\r -> r)
    , propMonoid @(P ()) (\r -> r)
    , propMonoid @(P [()]) (\r -> r)
    ]

instance (TestOb a, TestOb b) => TestableType (Pointed a b) where
  gen = invmap Pt unPt gen
  eqP (Pt l) (Pt r) = eqP l r
  showP (Pt f) = intercalate "," [showP x ++ "->" ++ maybe "*" showP (f x) | x <- enumAll]

instance Testable POINTED where
  type TestOb a = (Ob a, TestOb (UN P a))
  showOb @(P a) = showOb @_ @a
  genOb = genObDef @'[P Bool, P (Bool, Bool), P (Maybe Bool)]

instance (EnumAll a, EnumAll b) => EnumAll (These a b) where
  enumAll = (This <$> enumAll) ++ (That <$> enumAll) ++ (These <$> enumAll <*> enumAll)
instance (TestableType a, TestableType b) => TestableType (These a b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty l, GenEmpty r) -> GenEmpty \case
      This x -> l x
      That y -> r y
      These x _ -> l x
    (GenNonEmpty a ga, GenEmpty _) -> GenNonEmpty (This a) (This <$> ga)
    (GenEmpty _, GenNonEmpty b gb) -> GenNonEmpty (That b) (That <$> gb)
    (GenNonEmpty a ga, GenNonEmpty b gb) -> GenNonEmpty (These a b) (oneof [This <$> ga, That <$> gb, These <$> ga <*> gb])
  eqP (This l) (This r) = eqP l r
  eqP (That l) (That r) = eqP l r
  eqP (These l1 l2) (These r1 r2) = liftA2 (&&) (eqP l1 r1) (eqP l2 r2)
  eqP _ _ = pure False
  showP (This a) = "This " ++ showP a
  showP (That b) = "That " ++ showP b
  showP (These a b) = "These " ++ showP a ++ " " ++ showP b
instance (Function a, Function b) => Function (These a b)