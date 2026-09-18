{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.FinHask where

import Control.Monad (unless)
import Data.Map.Strict qualified as M
import Data.Type.Equality ((:~:) (..))
import Data.Universe.Class (Finite (..))
import Data.Universe.Helpers (Tagged (..))
import Data.Void (Void)
import GHC.TypeNats (KnownNat, withKnownNat, withSomeSNat)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)
import Prelude (($), (==))
import Prelude qualified as P

import Proarrow.Category.Enriched.Finitary (elements)
import Proarrow.Category.Instance.FinHask (FINHASK (..), Fin (..), FinHask (..))
import Proarrow.Core (CategoryOf (..), UN)

import Proarrow.Testing
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genOb
  , genSomeDef
  , oneElem
  , optGen
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Props.Hask ()
import Test.Falsify.Generator (minimalValue)
import Test.Tasty.Falsify (testFailed, testProperty)

test :: TestTree
test =
  testGroup
    "FinHask"
    [ propCategory @FINHASK
    , propTerminalObject @FINHASK
    , propInitialObject @FINHASK
    , propBinaryProducts @FINHASK (\r -> r)
    , propCartesian @FINHASK (\r -> r) (\r -> r)
    , propBinaryCoproducts @FINHASK (\r -> r)
    , propDistributive @FINHASK (\r -> r) (\r -> r)
    , propClosed @FINHASK (\r -> r) (\r -> r)
    , propEqualizers @FINHASK withTestObFinHaskViaFin
    , propCoequalizers @FINHASK withTestObFinHaskViaFin
    , propPullbacks @FINHASK withTestObFinHaskViaFin
    , propPushouts @FINHASK withTestObFinHaskViaFin
    , propFinitary @FinHask "FinHask"
    , testProperty "the numbering agrees with the universe" $ do
        -- 'propFinitary'\'s laws are all order-agnostic, so they would accept a numbering that
        -- disagreed with 'universe'; this is what pins the digit order.
        Some @a <- genOb @FINHASK
        Some @b <- genOb @FINHASK
        unless (elements @FinHask @a @b == universeF) (testFailed "elements should be universe, in order")
    ]

-- | Only ever pass this to 'propEqualizers', 'propCoequalizers', 'propPullbacks', or 'propPushouts':
-- it exploits the fact that 'HasEqualizers'\'s 'factorEqualizer', 'HasCoequalizers'\'s
-- 'factorCoequalizer', and 'HasPullbacks'\'s 'pullback' for 'FINHASK' all produce an object of the
-- form @FH (Fin n)@ (see their shared @reifyList@-based construction, which 'HasPushouts'\'s
-- @pushoutDefault@-based 'pushout' also goes through indirectly) -- a fact the type system has no way
-- to check. @n@ is recovered here from @e@'s cardinality, which must match since @Fin n@ has exactly
-- @n@ elements; the resulting (unsafely obtained) equality then borrows @Fin@'s existing
-- 'Typeable'/'TestableType' instances. Passing this to any other combinator (whose produced object
-- need not be 'Fin'-shaped, e.g. 'propBinaryProducts') would be unsound: same cardinality doesn't mean
-- same runtime representation.
withTestObFinHaskViaFin :: forall (e :: FINHASK) r. (Ob e) => ((TestOb e) => r) -> r
withTestObFinHaskViaFin body = case cardinality @(UN FH e) of
  Tagged n -> withSomeSNat n \ @m snat -> withKnownNat snat (case sameAsFin @m of Refl -> body)
  where
    sameAsFin :: forall m. UN FH e :~: Fin m
    sameAsFin = unsafeCoerce Refl

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
      GenNonEmpty g -> GenNonEmpty (FinHask P.. M.fromList P.<$> P.traverse (\a -> (a,) P.<$> g) universeF)
instance TestableProfunctor FinHask

instance (KnownNat n) => TestingEqShow (Fin n)
instance (KnownNat n) => TestableType (Fin n) where
  gen = case universeF of
    [] -> GenEmpty \(Fin i) -> P.error ("impossible Fin 0 value: " P.++ P.show i)
    xs -> optGen xs
