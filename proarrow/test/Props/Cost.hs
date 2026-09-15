{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Property tests for the cost category.
--
-- 'GTE' is thin: there is at most one arrow between any two objects, so arrow
-- equality is trivially true and the law properties cannot fail on a mismatch.
-- What they *do* establish is that every arrow the laws ask for can be built and
-- forced without hitting one of the supposedly-unreachable @error@ branches in
-- "Proarrow.Category.Instance.Cost", and that the type-level arithmetic lines up
-- at every object triple. 'eqP' below forces both sides for exactly that reason.
--
-- The paths worth covering are @associator@ \/ @associatorInv@ \/ @swap@, which
-- bridge associativity and commutativity of @+@ with 'unsafeCoerce', and
-- @distL@ \/ @distR@, whose branches rely on monotonicity of @+@.
module Props.Cost where

import Control.Monad (unless)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Ord (OrderingI (..))
import GHC.TypeNats (cmpNat, natVal)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude

import Proarrow.Category.Enriched.Matrix (Closure, Diagonal, Entry)
import Proarrow.Category.Instance.Cost (COST (..), GTE (..), IsCost (..), SCost (..))
import Proarrow.Core (Ob)

import Proarrow.Testing
  ( GenTotal (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , oneElem
  )
import Proarrow.Testing.Laws

test :: TestTree
test =
  testGroup
    "Cost"
    [ propCategory @COST
    , testProperty "GTE decidable" $ propDecidable @GTE
    , testProperty "shortest path P -> R is 7" $ case sing @(Closure COST Vs Diagonal G P R) of
        SC @n -> unless (natVal (Proxy @n) == 7) (testFailed "distance mismatch")
    , propTerminalObject @COST
    , propInitialObject @COST
    , propBinaryProducts_ @COST
    , propBinaryCoproducts_ @COST
    , propMonoidal_ @COST
    , propSymMonoidal_ @COST
    , propDistributive_ @COST
    , propEqualizers_ @COST
    , propCoequalizers_ @COST
    , propPullbacks_ @COST
    , propPushouts_ @COST
    ]

instance Testable COST where
  genSome = genSomeDef @'[C 0, C 1, C 2, C 3, INF]
  showOb @a = case sing @a of
    SINF -> "INF"
    SC @n -> "C " ++ show (natVal (Proxy @n))
  eqOb @a @b = case (sing @a, sing @b) of
    (SINF, SINF) -> Just Refl
    (SC @a', SC @b') -> case cmpNat (Proxy @a') (Proxy @b') of
      EQI -> Just Refl
      _ -> Nothing
    _ -> Nothing

instance (Ob a, Ob b) => TestableType (GTE a b) where
  gen = case (sing @a, sing @b) of
    (SINF, _) -> oneElem Inf
    -- No arrow from a finite cost to INF.
    (SC, SINF) -> GenEmpty \case {}
    (SC @a', SC @b') -> case cmpNat (Proxy @b') (Proxy @a') of
      LTI -> oneElem GTE
      EQI -> oneElem GTE
      -- b' > a', so the @b' <= a'@ that GTE demands is refutable.
      GTI -> GenEmpty \case {}

instance (Ob a, Ob b) => TestingEqShow (GTE a b) where
  -- Thin, so any two arrows with the same endpoints are equal -- but force both
  -- sides, so that a wrongly-taken error branch surfaces as a test failure.
  eqP l r = l `seq` r `seq` pure True
  showP Inf = "Inf"
  showP GTE = "GTE"

instance TestableProfunctor GTE

-- * Shortest paths as a type-level fixed point

-- | A weighted graph: the direct edge @P -> R@ costs 9, the detour via @Q@ only 7; @T@ is isolated.
data V = P | Q | R | S | T

type family Weight (a :: V) (b :: V) :: COST where
  Weight P Q = C 3
  Weight Q R = C 4
  Weight P R = C 9
  Weight R S = C 2
  Weight S P = C 5
  Weight a b = INF

-- | The graph is not an enriched profunctor, only a matrix of weights: a tag with 'Entry's.
data G

type instance Entry COST G a b = Weight a b

type Vs = '[P, Q, R, S, T]

-- | The fixed point beats the direct edge.
distancePR :: Closure COST Vs Diagonal G P R :~: C 7
distancePR = Refl

-- | Around the cycle: @Q -> R -> S -> P@.
distanceQP :: Closure COST Vs Diagonal G Q P :~: C 11
distanceQP = Refl

-- | Every point is at distance @0@ from itself, and an isolated point is infinitely far.
distancePP :: Closure COST Vs Diagonal G P P :~: C 0
distancePP = Refl

distancePT :: Closure COST Vs Diagonal G P T :~: INF
distancePT = Refl
