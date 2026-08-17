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

import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Ord (OrderingI (..))
import GHC.TypeNats (cmpNat, natVal)
import Test.Tasty (TestTree, testGroup)
import Prelude

import Proarrow.Category.Instance.Cost (COST (..), GTE (..), IsCost (..), SCost (..))
import Proarrow.Core (Ob)

import Props
import Testable
  ( GenTotal (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , oneElem
  )

test :: TestTree
test =
  testGroup
    "Cost"
    [ propCategory @COST
    , propTerminalObject @COST
    , propInitialObject @COST
    , propBinaryProducts_ @COST
    , propBinaryCoproducts_ @COST
    , propMonoidal_ @COST
    , propSymMonoidal_ @COST
    , propDistributive_ @COST
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
