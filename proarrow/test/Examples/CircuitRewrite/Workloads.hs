-- | Circuit families for checking repeated rewriting, sharing, and fixed points.
-- Sizes count redundant cells or parallel leaves.
module Examples.CircuitRewrite.Workloads (chain, parallelBranches, sharedSignals) where

import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.Circuit
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..))

-- | Four gates implementing the identity. Double negation and AND identity apply.
cell :: Bit ~> Bit
cell = notGate . notGate . andGate . (constant True ** obj @Bit) . leftUnitorInv

-- | @4*n@ gates reduce to wiring, using @2*n@ steps.
chain :: Int -> Circuit Bit Bit
chain n = foldr (.) id (replicate n cell)

-- | Independent redundant branches, combined by a balanced AND tree.
-- For positive @n@, @5*n-1@ gates reduce to wiring in @3*n-1@ steps.
parallelBranches :: Int -> Circuit Bit Bit
parallelBranches n = branches n cell

-- | Both inverter outputs feed an AND. Double negation preserves the shared
-- inverter, then complement elimination gives false. For positive @n@,
-- @4*n-1@ gates reduce to false in @3*n-1@ steps.
sharedSignals :: Int -> Circuit Bit Bit
sharedSignals n = branches n (andGate . (obj @Bit ** notGate) . comult . notGate)

branches :: Int -> Circuit Bit Bit -> Circuit Bit Bit
branches n leaf
  | n <= 0 = id
  | n == 1 = leaf
  | otherwise = andGate . (branches l leaf ** branches (n - l) leaf) . comult
  where
    l = n `div` 2
