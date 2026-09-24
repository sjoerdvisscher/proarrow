{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- HLINT ignore "Use const" -}

module Props.FinHask where

import Data.Map.Strict qualified as M
import Data.Type.Equality ((:~:) (..))
import Data.Universe.Class (Finite (..))
import Data.Universe.Helpers (Tagged (..))
import Data.Void (Void)
import GHC.TypeNats (KnownNat, withKnownNat, withSomeSNat)
import Test.Tasty (TestTree, testGroup)
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)
import Prelude (pure, ($))
import Prelude qualified as P

import Proarrow.Category.Enriched.Finitary (elements)
import Proarrow.Category.Instance.FinHask (FINHASK (..), Fin (..), FinHask (..), fromList)
import Proarrow.Core (CategoryOf (..), UN)

import Proarrow.Testing
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , expect
  , genOb
  , genSomeDef
  , oneElem
  , optGen
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Proarrow.Tools.DPO (pushoutComplement)
import Props.Hask ()
import Test.Falsify.Generator (minimalValue)
import Test.Tasty.Falsify (testFailed, testProperty)

test :: TestTree
test =
  testGroup
    "FinHask"
    [ testCategory @FINHASK
    , testTerminalObject @FINHASK
    , testInitialObject @FINHASK
    , testBinaryProducts @FINHASK (\r -> r)
    , testCartesian @FINHASK (\r -> r) (\r -> r)
    , testMonoidal @FINHASK (\r -> r)
    , testMonoidalHom @FINHASK (\r -> r)
    , testSymMonoidal @FINHASK (\r -> r)
    , testCopyDiscard @FINHASK (\r -> r) (\r -> r)
    , testBinaryCoproducts @FINHASK (\r -> r)
    , testDistributive @FINHASK (\r -> r) (\r -> r)
    , testClosed @FINHASK (\r -> r) (\r -> r)
    , testEqualizers @FINHASK withTestObFinHaskViaFin
    , testCoequalizers @FINHASK withTestObFinHaskViaFin
    , testEpiMonoFactorization @FINHASK withTestObFinHaskViaFin
    , testSubobjectClassifier @FINHASK (\r -> r)
    , testPullbacks @FINHASK withTestObFinHaskViaFin
    , testPushouts @FINHASK withTestObFinHaskViaFin
    , testFinitary @FinHask "FinHask"
    , testProperty "a pushout complement deletes what the rule does not keep" $
        -- a : Fin 1 -> l : Fin 2 keeps one of two elements; the match is the identity on Fin 2, so
        -- the complement is the one kept element
        pushoutComplement
          (fromList [(0 :: Fin 1, 0 :: Fin 2)])
          (fromList [(0 :: Fin 2, 0 :: Fin 2), (1, 1)])
          (\_ (FinHask d) -> expect "the complement is the kept element" [0 :: Fin 2] (M.elems d))
          (testFailed "should have been glueable")
    , testProperty "a match identifying a kept element with a deleted one is refused" $
        -- both elements of l map to 0, but the rule keeps only one of them
        pushoutComplement
          (fromList [(0 :: Fin 1, 0 :: Fin 2)])
          (fromList [(0 :: Fin 2, 0 :: Fin 1), (1, 0)])
          (\_ _ -> testFailed "should not have been glueable")
          (pure ())
    , testProperty "a match identifying two deleted elements is refused" $
        -- neither element of l is kept, and both map to 0, so no pushout complement exists
        pushoutComplement
          (fromList [] :: FinHask (FH (Fin 0)) (FH (Fin 2)))
          (fromList [(0 :: Fin 2, 0 :: Fin 1), (1, 0)])
          (\_ _ -> testFailed "should not have been glueable")
          (pure ())
    , testProperty "the numbering agrees with the universe" $ do
        -- 'testFinitary'\'s laws are all order-agnostic, so they would accept a numbering that
        -- disagreed with 'universe'; this is what pins the digit order.
        Some @a <- genOb @FINHASK
        Some @b <- genOb @FINHASK
        expect "elements should be the universe, in order" universeF (elements @FinHask @a @b)
    ]

-- | Only for 'testEqualizers', 'testCoequalizers', 'testPullbacks' and 'testPushouts': it assumes
-- the object is @FH (Fin n)@, as the 'FINHASK' equalizer, coequalizer, pullback and pushout
-- constructions (all via @reifyList@) produce, which the types cannot check. @n@ is recovered from
-- @e@'s cardinality and the equality is coerced, borrowing @Fin@'s 'Typeable'\/'TestableType'
-- instances. Elsewhere (e.g. 'testBinaryProducts') this is unsound: same cardinality is not same
-- runtime representation.
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
