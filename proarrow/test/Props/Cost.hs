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
import Data.Type.Nat (Nat (..), SNat (..), snat)
import Data.Type.Ord (OrderingI (..))
import GHC.TypeNats (cmpNat, natVal)
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude

import Proarrow.Category.Enriched (EnrichedProfunctor (..))
import Proarrow.Category.Enriched.Thin (Finite (..), Indexed (..), IndexedList (..))
import Proarrow.Category.Enriched.Thin.Composition (Closure, GradedWalk (..), Length, shortest)
import Proarrow.Category.Instance.Cost (COST (..), GTE (..), IsCost (..), SCost (..))
import Proarrow.Category.Instance.Discrete (DISCRETE (..))
import Proarrow.Core (Ob)
import Proarrow.Profunctor.Instance.Edges (Edges)

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
    , testProperty "shortest paths computed at the value level" $ do
        unless (distance @(D P) @(D R) == Just 7) (testFailed "P -> R should be 7")
        unless (distance @(D Q) @(D P) == Just 11) (testFailed "Q -> P should be 11")
        unless (distance @(D P) @(D P) == Just 0) (testFailed "P -> P should be 0")
        unless (distance @(D P) @(D Y) == Nothing) (testFailed "P -> Y should be unreachable")
    , testProperty "shortest paths as witnesses" $ do
        unless (steps (shortest @COST @N @G @(D P) @(D R)) == 2) (testFailed "P -> R should take the detour via Q")
        unless (steps (shortest @COST @N @G @(D Q) @(D P)) == 3) (testFailed "Q -> P should go around the cycle")
        unless (steps (shortest @COST @N @G @(D P) @(D P)) == 0) (testFailed "P -> P should stay put")
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

-- * Shortest paths as a fixed point, at the type level and at the value level

-- | Five points; the direct edge @P -> R@ costs 9, the detour via @Q@ only 7, and @Y@ is isolated.
data V = P | Q | R | X | Y

instance Indexed V where
  type Index P = 'Z
  type Index Q = 'S 'Z
  type Index R = 'S ('S 'Z)
  type Index X = 'S ('S ('S 'Z))
  type Index Y = 'S ('S ('S ('S 'Z)))
  type At V 'Z = 'Just P
  type At V ('S 'Z) = 'Just Q
  type At V ('S ('S 'Z)) = 'Just R
  type At V ('S ('S ('S 'Z))) = 'Just X
  type At V ('S ('S ('S ('S 'Z)))) = 'Just Y
  type At V ('S ('S ('S ('S ('S i))))) = 'Nothing

instance Finite V where
  type Objects V = '[P, Q, R, X, Y]
  finite = FCons (FCons (FCons (FCons (FCons FNil))))
  atLookup SZ = Refl
  atLookup (SS @i1) = case snat @i1 of
    SZ -> Refl
    SS @i2 -> case snat @i2 of
      SZ -> Refl
      SS @i3 -> case snat @i3 of
        SZ -> Refl
        SS @i4 -> case snat @i4 of
          SZ -> Refl
          SS -> Refl

type G = Edges '[ '(P, Q, C 3), '(Q, R, C 4), '(P, R, C 9), '(R, X, C 2), '(X, P, C 5)]

-- | The fixed point beats the direct edge.
distancePR :: ProObj COST (Closure G) (D P) (D R) :~: C 7
distancePR = Refl

-- | Around the cycle: @Q -> R -> X -> P@.
distanceQP :: ProObj COST (Closure G) (D Q) (D P) :~: C 11
distanceQP = Refl

-- | Every point is at distance @0@ from itself, and an isolated point is infinitely far.
distancePP :: ProObj COST (Closure G) (D P) (D P) :~: C 0
distancePP = Refl

distancePY :: ProObj COST (Closure G) (D P) (D Y) :~: INF
distancePY = Refl

-- | The same computation at the value level: the points are abstract here, so the distance singleton
-- can only come from 'withProObj' running the fixed point.
distance :: forall (a :: DISCRETE V) (b :: DISCRETE V). (Ob a, Ob b) => Maybe Natural
distance = withProObj @COST @(Closure G) @a @b case sing @(ProObj COST (Closure G) a b) of
  SC @n -> Just (natVal (Proxy @n))
  SINF -> Nothing

type N = Length (Objects (DISCRETE V))

-- | The shortest walk from @P@ to @R@ has grade @7@ by type, and two steps by value.
shortestPR :: GradedWalk COST N G (C 7) (D P) (D R)
shortestPR = shortest

steps :: GradedWalk v n p d a b -> Int
steps (DoneAt _) = 0
steps (StepAt _ w) = 1 + steps w
