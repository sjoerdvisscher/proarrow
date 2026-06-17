{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Bool where

import Data.Type.Equality ((:~:) (Refl))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (discard, testProperty)
import Prelude

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..), NonTrivialProfunctor (..))
import Proarrow.Core (Ob, obj)

import Proarrow.Category.Instance.Product ((:**:) (..))
import Props
import Testable
  ( GenTotal (..)
  , SomeProfunctorElt (..)
  , Testable (..)
  , TestableProfunctor (..)
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , one
  , someElemNamed
  )

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

instance (Ob a, Ob b) => TestableType (Booleans a b) where
  gen = case (obj @a, obj @b) of
    (Fls, Fls) -> one Fls
    (Fls, Tru) -> one F2T
    (Tru, Tru) -> one Tru
    (Tru, Fls) -> GenEmpty \case {}
instance (Ob a, Ob b) => TestingEqShow (Booleans a b) where
  eqP _ _ = pure True
  showP Fls = "F->F"
  showP F2T = "F->T"
  showP Tru = "T->T"
instance TestableProfunctor Booleans

instance (Ob ft) => TestableProfunctor (NonTrivialProfunctor ft) where
  genProfunctorElt nm = case obj @ft of
    Tru :**: Fls -> someElemNamed nm [SomeP FF, SomeP FT]
    Tru :**: Tru -> someElemNamed nm [SomeP FF, SomeP FT, SomeP TT]
    Fls :**: Tru -> someElemNamed nm [SomeP FT, SomeP TT]
    Fls :**: Fls -> discard
instance (Ob ft, TestOb a, TestOb b) => TestingEqShow (NonTrivialProfunctor ft a b)
