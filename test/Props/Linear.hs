{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Linear where

import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.Linear (LINEAR (..), Linear (..), Top (..), With (..), mkWith, unsafeLinear)
import Proarrow.Core (CategoryOf (..), UN)

import Props
import Props.Hask ()
import Test.Falsify.Generator (Function (..))
import Testable (GenTotal (..), Testable (..), TestableType (..), genObDef, invmap, one, pattern GenNonEmpty)

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
    , propSymMonoidal @LINEAR (\r -> r)
    , propClosed @LINEAR (\r -> r) (\r -> r)
    ]

instance (TestOb a, TestOb b) => TestableType (Linear a b) where
  gen = invmap Linear (\(Linear f) -> f) gen
  eqP (Linear l) (Linear r) = eqP l r
  showP (Linear f) = showP f

instance Testable LINEAR where
  type TestOb a = (Ob a, TestOb (UN L a))
  showOb @(L a) = showOb @_ @a
  genOb = genObDef @'[L Bool, L (Bool, Bool), L (Maybe Bool)]

instance (TestOb a, TestOb b) => TestableType (a %1 -> b) where
  gen = invmap unsafeLinear (\f a -> f a) gen
  eqP l r = eqP (\a -> l a) (\a -> r a)
  showP f = showP (\a -> f a)
instance (TestableType a, TestableType b) => TestableType (With a b) where
  gen = case (gen @a, gen @b) of
    (GenEmpty absurd, _) -> GenEmpty \(With x xa _) -> absurd (xa x)
    (_, GenEmpty absurd) -> GenEmpty \(With x _ xb) -> absurd (xb x)
    (GenNonEmpty ga, GenNonEmpty gb) -> GenNonEmpty (mkWith <$> ga <*> gb)
  eqP (With x fa fb) (With y ga gb) = liftA2 (&&) (eqP (fa x) (ga y)) (eqP (fb x) (gb y))
  showP (With x fa fb) = "mkWith " ++ showP (fa x) ++ " " ++ showP (fb x)
instance TestableType Top where
  gen = one (Top ())
  eqP _ _ = pure True
  showP (Top _) = "⊤"

-- Unused instances
instance Function (a %1 -> b) where
  function = undefined
instance Function (With a b) where
  function = undefined
instance Function Top where
  function = undefined
