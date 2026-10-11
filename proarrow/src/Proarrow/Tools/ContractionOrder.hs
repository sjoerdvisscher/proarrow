-- | The order to contract a network of factors in, such as a tensor network or the states of an
-- open hypergraph: which two to contract first, then which two of the factors and results, and so
-- on. Contracting two factors makes a factor on the nodes of both that something else still needs,
-- so its size depends on the order, and a bad order can make the intermediate results far larger
-- than the network itself.
--
-- 'planContraction' makes two plans and takes the one whose contractions are smaller together:
-- numpy's greedy order, and an elimination order of the nodes from the min-fill heuristic for tree
-- decompositions, as in Peterseim and Lopuhaä-Zwakenberg, /Fixed-Parameter Tractable Inference for
-- Discrete Probabilistic Programs, via String Diagram Algebraisation/ (LICS 2026).
module Proarrow.Tools.ContractionOrder (Plan (..), planContraction, minFillOrder) where

import Data.Containers.ListUtils (nubOrd)
import Data.List qualified as List
import Data.Map.Strict qualified as M
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set qualified as Set
import Prelude

-- | A plan to contract factors: one of them, by its place in the list, or the contraction of the
-- results of two plans.
data Plan = Factor Int | Contract Plan Plan
  deriving (Eq, Show)

-- | A part of a plan: its plan, how many of its factors touch each node, the nodes something
-- outside it needs, and the size of its contractions together.
data Part n = Part {plan :: Plan, counts :: M.Map n Int, open :: Set n, cost :: ~Double}

-- | Plans to contract the given factors, each given by its nodes, until no two of the results share
-- a node that may be contracted: a plan for each result. A result keeps the nodes that the given
-- set needs or that factors outside it touch, and its size is the size of those nodes. Of numpy's
-- greedy order, which contracts the pair that shares such a node and whose result grows least, its
-- size less those of the two parts, and of the min-fill elimination order of those nodes, which
-- contracts the parts on each node in turn, the pair that grows least first, the plan whose
-- contractions are smaller together is taken.
--
-- >>> planContraction (fromIntegral . length) (const True) mempty [Set.fromList "ab", Set.fromList "bc", Set.fromList "cd"]
-- [Contract (Contract (Factor 0) (Factor 1)) (Factor 2)]
planContraction :: (Ord n) => (Set n -> Double) -> (n -> Bool) -> Set n -> [Set n] -> [Plan]
planContraction size contractible needed factors
  -- with at most two factors on contractible nodes there is only one plan
  | [i, j] <- candidates =
      if any contractible (Set.intersection (factors !! i) (factors !! j))
        then Contract (Factor i) (Factor j) : others i j
        else alone
  | [_] <- candidates = alone
  | [] <- candidates = alone
  | all (isFactor . plan) greedy = plan <$> greedy
  | otherwise = plan <$> if total greedy <= total eliminated then greedy else eliminated
  where
    candidates = [i | (i, f) <- zip [0 ..] factors, any contractible f]
    alone = Factor <$> [0 .. length factors - 1]
    others i j = [Factor k | k <- [0 .. length factors - 1], k /= i, k /= j]
    leaves = [part (Factor i) (M.fromSet (const 1) f) 0 | (i, f) <- zip [0 ..] factors]
    greedy = contract leaves
    eliminated = along (minFillOrder (size . Set.fromList) (Set.toList . open <$> leaves) nodes) leaves
    total ps = sum (cost <$> ps)
    nodes = nubOrd [n | f <- factors, n <- Set.toList f, contractible n]
    totals = M.fromListWith (+) [(n, 1) | f <- factors, n <- Set.toList f]
    part p cs c = Part p cs (M.keysSet (M.filterWithKey (\n k -> k < totals M.! n || n `Set.member` needed) cs)) c
    merge a b =
      part
        (Contract (plan a) (plan b))
        (M.unionWith (+) (counts a) (counts b))
        (cost a + cost b + size (Set.union (open a) (open b)))
    isFactor Factor{} = True
    isFactor Contract{} = False
    shares a b = any contractible (Set.intersection (open a) (open b))
    pairsOf ps = [(a, b) | a : rest <- List.tails ps, b <- rest]
    -- of the given pairs, the one whose contraction grows least, with that contraction
    best pairs = case [(size (open ab) - size (open a) - size (open b), (a, b, ab)) | (a, b) <- pairs, let ab = merge a b] of
      [] -> Nothing
      cs -> Just (snd (List.minimumBy (comparing fst) cs))
    replaced a b ab ps = [if plan q == plan a then ab else q | q <- ps, plan q /= plan b]
    contract ps = case best [(a, b) | (a, b) <- pairsOf ps, shares a b] of
      Just (a, b, ab) -> contract (replaced a b ab ps)
      Nothing -> ps
    along [] ps = ps
    along (n : ns) ps = case best (pairsOf [p | p <- ps, n `Set.member` open p]) of
      Just (a, b, ab) -> along (n : ns) (replaced a b ab ps)
      Nothing -> along ns ps

-- | An order to eliminate the given vertices of a graph in, by the min-fill heuristic for tree
-- decompositions. The graph has an edge between any two vertices of a common clique. Eliminating a
-- vertex joins its neighbours, so the next vertex is the one whose neighbours lack the fewest edges
-- among themselves, and of those the one whose neighbours weigh least together. A star is
-- eliminated from its leaves:
--
-- >>> minFillOrder length [[0, 1], [0, 2], [0, 3 :: Int]] [0, 1, 2, 3]
-- [1,2,0,3]
minFillOrder :: (Ord a, Ord w) => ([a] -> w) -> [[a]] -> [a] -> [a]
minFillOrder weight cliques = go graph
  where
    graph = M.fromListWith Set.union [(v, Set.fromList (filter (/= v) c)) | c <- cliques, v <- c]
    neighbours g v = M.findWithDefault Set.empty v g
    go _ [] = []
    go g vs =
      let v = List.minimumBy (comparing (fill g)) vs
          nbs = neighbours g v
          -- only the neighbours of v change: they lose v and become adjacent to each other
          joined = foldr (\u -> M.adjust (Set.delete u . Set.union nbs . Set.delete v) u) (M.delete v g) (Set.toList nbs)
      in v : go joined (List.delete v vs)
    fill g v =
      let nbs = Set.toList (neighbours g v)
      in (length [() | (a : rest) <- List.tails nbs, let na = neighbours g a, b <- rest, not (b `Set.member` na)], weight nbs)
