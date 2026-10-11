-- | Contraction plans: each factor is used once, each contraction joins two parts that share a node
-- that may be contracted, and no two results share such a node.
module Props.ContractionOrder (test) where

import Control.Monad (replicateM)
import Data.List (sort)
import Data.Set (Set)
import Data.Set qualified as Set
import Test.Falsify (Property)
import Test.Falsify qualified as F
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (elem)

import Proarrow.Testing (check)
import Proarrow.Tools.ContractionOrder (Plan (..), planContraction)

-- | Factors on up to eight nodes, the nodes needed outside, and which nodes may be contracted.
network :: Property ([Set Int], Set Int, Int -> Bool)
network = do
  k <- F.gen (elem [1 .. 8])
  factors <- replicateM k do
    arity <- F.gen (elem [1 .. 3])
    Set.fromList <$> replicateM arity (F.gen (elem [0 .. 7]))
  needed <- Set.fromList <$> replicateM 2 (F.gen (elem [0 .. 7]))
  cut <- F.gen (elem [0 .. 8])
  pure (factors, needed, (< cut))

-- | The factors of a plan.
factorsOf :: Plan -> [Int]
factorsOf (Factor i) = [i]
factorsOf (Contract a b) = factorsOf a ++ factorsOf b

-- | The plans for a network, with the nodes something outside each part needs.
planned :: ([Set Int], Set Int, Int -> Bool) -> ([Plan], Plan -> Set Int)
planned (factors, needed, contractible) = (planContraction (fromIntegral . Set.size) contractible needed factors, open)
  where
    open p =
      let inside = factorsOf p
          nodes = Set.unions [factors !! i | i <- inside]
          outside = Set.unions [f | (i, f) <- zip [0 ..] factors, i `notElem` inside]
      in Set.filter (\n -> n `Set.member` needed || n `Set.member` outside) nodes

test :: TestTree
test =
  testGroup
    "Contraction order"
    [ testProperty "each factor is used once" do
        net@(factors, _, _) <- network
        let (ps, _) = planned net
        check ("plans " ++ show ps) (sort (concatMap factorsOf ps) == [0 .. length factors - 1])
    , testProperty "each contraction joins two parts that share a node that may be contracted" do
        net@(_, _, contractible) <- network
        let (ps, open) = planned net
            joins (Factor _) = True
            joins (Contract a b) = any contractible (Set.intersection (open a) (open b)) && joins a && joins b
        check ("plans " ++ show ps) (all joins ps)
    , testProperty "no two results share a node that may be contracted" do
        net@(_, _, contractible) <- network
        let (ps, open) = planned net
        check
          ("plans " ++ show ps)
          ( and
              [ not (any contractible (Set.intersection (open p) (open q)))
              | (i, p) <- zip [0 :: Int ..] ps
              , (j, q) <- zip [0 ..] ps
              , i < j
              ]
          )
    ]
