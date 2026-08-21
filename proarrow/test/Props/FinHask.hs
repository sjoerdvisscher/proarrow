{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
    , propEqualizers @FINHASK withTestObFinHaskViaFin
    , propCoequalizers @FINHASK withTestObFinHaskViaFin
    , propPullbacks @FINHASK withTestObFinHaskViaFin
    , propPushouts @FINHASK withTestObFinHaskViaFin
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
