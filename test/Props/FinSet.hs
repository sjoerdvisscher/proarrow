{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FinSet where

import Data.Fin (Fin, absurd, universe)
import Data.Type.Equality (TestEquality(..), type (:~:) (..))
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3, Nat4, SNat (..), SNatI, snat)
import Data.Vec.Lazy (Vec (..), repeat)
import Test.Tasty (TestTree, testGroup)
import Prelude qualified as P

import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Core (CategoryOf (..))

import Props
import Testable
  ( GenTotal (..)
  , Testable (..)
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , invmap
  , one
  , optGen
  , pattern GenNonEmpty
  )

test :: TestTree
test =
  testGroup
    "FinSet"
    [ propCategory @FINSET
    , propTerminalObject @FINSET
    , propInitialObject @FINSET
    , propBinaryProducts_ @FINSET
    , propBinaryCoproducts_ @FINSET
    , propClosed_ @FINSET
    , testComonoid_ @(FS Nat0)
    , testComonoid_ @(FS Nat1)
    , testComonoid_ @(FS Nat2)
    , testComonoid_ @(FS Nat3)
    , testMonoid_ @(FS Nat1)
    ]

instance Testable FINSET where
  type TestOb a = Ob a
  showOb @(FS a) = P.show (snat @a)
  eqOb @(FS a) @(FS b) = (\Refl -> Refl) P.<$> testEquality (snat @a) (snat @b)
  genSome = genSomeDef @'[FS Nat1, FS Nat2, FS Nat3, FS Nat4]

instance (Ob a, Ob b) => TestingEqShow (FinSet a b)
instance (Ob a, Ob b) => TestableType (FinSet a b) where
  gen = invmap FinSet unFinSet gen

instance (P.Eq a, P.Show a) => TestingEqShow (Vec n a)
instance (P.Eq a, P.Show a, TestableType a, SNatI n) => TestableType (Vec n a) where
  gen = case gen of
    GenEmpty absrd -> case snat @n of
      SZ -> one VNil
      SS -> GenEmpty \(a ::: _) -> absrd a
    GenNonEmpty g -> GenNonEmpty (P.sequence (repeat @n g))

instance (SNatI n) => TestingEqShow (Fin n)
instance (SNatI n) => TestableType (Fin n) where
  gen = case snat @n of
    SZ -> GenEmpty absurd
    SS -> optGen universe
