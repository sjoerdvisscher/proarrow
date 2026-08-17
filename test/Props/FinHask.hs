{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FinHask where

import Data.Map.Strict qualified as M
import Data.Universe.Class (Finite (..))
import Data.Void (Void)
import GHC.TypeLits (KnownNat)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Prelude qualified as P

import Proarrow.Category.Instance.FinHask (FINHASK (..), Fin (..), FinHask (..))
import Proarrow.Core (CategoryOf (..), UN)

import Props
import Props.Hask ()
import Test.Falsify.Generator (minimalValue)
import Testable
  ( GenTotal (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , oneElem
  , optGen
  , pattern GenNonEmpty
  )

test :: TestTree
test =
  testGroup
    "FinHask"
    [ propCategory @FINHASK
    , propTerminalObject @FINHASK
    , propInitialObject @FINHASK
    , propBinaryProducts @FINHASK (\r -> r)
    , propBinaryCoproducts @FINHASK (\r -> r)
    , propDistributive @FINHASK (\r -> r) (\r -> r)
    , propClosed @FINHASK (\r -> r) (\r -> r)
    ]

instance Testable FINHASK where
  type TestOb a = (Ob a, Typeable (UN FH a), TestableType (UN FH a))
  showOb @(FH a) = P.show (typeRep @a)
  genSome = genSomeDef @'[FH Void, FH (), FH P.Bool, FH (Fin 3)]

instance (Ob a, Ob b) => TestingEqShow (FinHask a b)
instance (TestOb a, TestOb b) => TestableType (FinHask a b) where
  gen =
    case gen @(UN FH b) of
      GenEmpty absurd -> case gen @(UN FH a) of
        GenEmpty _ -> oneElem (FinHask M.empty)
        GenNonEmpty g -> GenEmpty \(FinHask m) -> absurd (m M.! minimalValue g)
      GenNonEmpty g -> GenNonEmpty (FinHask P.. M.fromList P.<$> (P.traverse (\a -> (a,) P.<$> g) universeF))
instance TestableProfunctor FinHask

instance (KnownNat n) => TestingEqShow (Fin n)
instance (KnownNat n) => TestableType (Fin n) where
  gen = optGen universeF
