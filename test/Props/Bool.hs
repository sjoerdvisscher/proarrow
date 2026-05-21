{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Bool where

import Data.Type.Equality ((:~:)(Refl))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), NonTrivialProfunctor (..))
import Proarrow.Core (obj, Ob)

import Props
import Testable (GenTotal (..), Testable (..), TestableType (..), genSomeDef, one, TestingEqShow (..))
import Proarrow.Category.Instance.Product ((:**:)(..))

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
    , testProperty "FT profunctor" $ propProfunctor @(NonTrivialProfunctor '(FLS, FLS))
    , testProperty "FF,FT profunctor" $ propProfunctor @(NonTrivialProfunctor '(TRU, FLS))
    , testProperty "FT,TT profunctor" $ propProfunctor @(NonTrivialProfunctor '(FLS, TRU))
    , testProperty "FF,FT,TT profunctor" $ propProfunctor @(NonTrivialProfunctor '(TRU, TRU))
    ]

instance Testable BOOL where
  showOb @a = case obj @a of
    Fls -> "FLS"
    Tru -> "TRU"
  eqOb @a @b = case (obj @a, obj @b) of
    (Fls, Fls) -> Just Refl
    (Tru, Tru) -> Just Refl
    _ -> Nothing
  genSome = genSomeDef @'[FLS, TRU]

instance (TestOb a, TestOb b) => TestableType (Booleans a b) where
  gen = case (obj @a, obj @b) of
    (Fls, Fls) -> one Fls
    (Fls, Tru) -> one F2T
    (Tru, Tru) -> one Tru
    (Tru, Fls) -> GenEmpty \case {}
instance (TestOb a, TestOb b) => TestingEqShow (Booleans a b) where
  eqP _ _ = pure True
  showP Fls = "F->F"
  showP F2T = "F->T"
  showP Tru = "T->T"

instance (Ob ft, TestOb a, TestOb b) => TestableType (NonTrivialProfunctor ft a b) where
  gen = case (obj @ft, obj @a, obj @b) of
    (Tru :**: _, Fls, Fls) -> one FF
    (_, Fls, Tru) -> one FT
    (_ :**: Tru, Tru, Tru) -> one TT
    _ -> GenEmpty \case {}
instance (Ob ft, TestOb a, TestOb b) => TestingEqShow (NonTrivialProfunctor ft a b)
