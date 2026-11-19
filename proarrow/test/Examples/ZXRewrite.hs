{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Clifford+T diagrams simplified by the hypergraph rewriting engine.
-- Spiders remain explicit boxes; wiring denotes qubit contraction. Rules are
-- parameterised by phase and capture port lists of arbitrary degree.
module Examples.ZXRewrite where

import Control.Monad (filterM, replicateM, unless, when)
import Data.Bifunctor (bimap)
import Data.Bits (shiftL, testBit, xor)
import Data.Complex (Complex, mkPolar)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (isLeft)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List (find, mapAccumL, subsequences)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as Map
import Data.Ratio (denominator, numerator)
import GHC.TypeNats (Nat)
import System.Random (mkStdGen, uniformR)
import Test.Falsify (Property, testFailed)
import Test.Falsify qualified as Falsify
import Test.Falsify.Generator qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (TestOptions (..), testProperty, testPropertyWith)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.ZX qualified as ZX
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj, (//))
import Proarrow.Object (ListOf (..), withKnownListOf)
import Proarrow.Testing (check, expect)
import Proarrow.Testing.Laws (defaultTestOptions)
import Proarrow.Tools.HypergraphRewrite qualified as R

-- Phases are rational multiples of pi, normalised modulo 2 at construction.
data Colour = Z | X deriving (Eq, Ord, Show)

-- Scalar power angle denotes sqrt(2)^power * exp(i*pi*angle).
-- Selected and Pivot mark the spiders of one explicitly requested expansion.
data Generator a = Spider Colour a | Hadamard | Scalar Int Rational | Selected a | Pivot Bool a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Diagram = HG.OPENHG () (Generator Rational)
type Q = HG.Wires '[ '()] :: Diagram
type QQ = HG.Wires '[ '(), '()] :: Diagram
type SomeDiagram = HG.SomeHypergraph () (Generator Rational)

phase :: Rational -> Rational
phase a = a - 2 * fromInteger (floor (a / 2))

spider
  :: forall as bs. (HG.SortList as, HG.SortList bs) => Colour -> Rational -> (HG.Wires as :: Diagram) ~> HG.Wires bs
spider c a = HG.box (Spider c (phase a))

h :: Q ~> Q
h = HG.box Hadamard

z, x :: Rational -> Q ~> Q
z = spider Z
x = spider X

-- Like the existing ZX.cnot, this uses unnormalised spiders: the diagram
-- denotes CNOT / sqrt 2. We retain this scalar throughout simplification.
cnot :: QQ ~> QQ
cnot = (obj @Q ** spider @'[ '(), '()] @'[ '()] X 0) . (spider @'[ '()] @'[ '(), '()] Z 0 ** obj @Q)

-- A gate list keeps generation independent of diagram construction. Qubits
-- are numbered left to right; phases are rational multiples of pi.
data CircuitGate = CNot Int Int | Had Int | ZPhase Int Rational
  deriving (Eq, Show)

-- The default PyZX CNOT_HAD_PHASE distribution: 60% CNOT, 20% H, 20% T.
-- Depth counts gates, not parallel layers. Seeds are reproducible with random's
-- StdGen; they do not reproduce Python's random.Random sequences.
cnotHadPhaseCircuit :: Int -> Int -> Int -> Either String [CircuitGate]
cnotHadPhaseCircuit qubits depth seed = do
  unless (qubits >= 2) (Left "cnotHadPhaseCircuit: need at least two qubits")
  unless (depth >= 0) (Left "cnotHadPhaseCircuit: negative gate count")
  pure (go depth (mkStdGen seed))
  where
    go 0 _ = []
    go remaining rng =
      let (kind, rng1) = uniformR (0 :: Int, 4) rng
          (q, rng2) = uniformR (0, qubits - 1) rng1
          (other, rng3) = uniformR (0, qubits - 2) rng2
          target = if other < q then other else other + 1
          (gate, next) = case kind of
            4 -> (Had q, rng2)
            3 -> (ZPhase q (1 / 4), rng2)
            _ -> (CNot q target, rng3)
      in gate : go (remaining - 1) next

-- Build the circuit wiring directly, keeping the frontier in qubit order.
-- Each CNOT adds sqrt(2): our unnormalised Z/X spider pair alone denotes
-- CNOT/sqrt(2). The generated circuit therefore has ordinary unitary semantics.
circuitDiagram :: Int -> [CircuitGate] -> Either String SomeDiagram
circuitDiagram qubits gates = do
  unless (qubits >= 0) (Left "circuitDiagram: negative qubit count")
  let validQ q = q >= 0 && q < qubits
      valid (CNot c t) = validQ c && validQ t && c /= t
      valid (Had q) = validQ q
      valid (ZPhase q _) = validQ q
  unless (all valid gates) (Left "circuitDiagram: invalid gate qubit")
  let step (next, frontier, boxes, power) gate = case gate of
        CNot c t ->
          ( next + 3
          , IM.insert c next (IM.insert t (next + 1) frontier)
          , HG.Box (Spider X 0) [next + 2, frontier IM.! t] [next + 1]
              : HG.Box (Spider Z 0) [frontier IM.! c] [next, next + 2]
              : boxes
          , power + 1
          )
        Had q -> (next + 1, IM.insert q next frontier, HG.Box Hadamard [frontier IM.! q] [next] : boxes, power)
        ZPhase q p -> (next + 1, IM.insert q next frontier, HG.Box (Spider Z (phase p)) [frontier IM.! q] [next] : boxes, power)
      (end, outputs, built, cnots) = foldl' step (qubits, IM.fromList [(i, i) | i <- [0 .. qubits - 1]], [], 0) gates
  pure
    (someDiagram end [0 .. qubits - 1] (IM.elems outputs) (reverse built ++ [HG.Box (Scalar cnots 0) [] [] | cnots /= 0]))

data DiagramSize = DiagramSize {sizeSpiders :: Int, sizeHadamards :: Int, sizeNonClifford :: Int}
  deriving (Eq, Show)

diagramSize :: (a :: Diagram) ~> b -> DiagramSize
diagramSize graph =
  let (_, _, _, boxes) = HG.hypergraphParts graph
  in DiagramSize
       (spiderCount graph)
       (length [() | HG.Box Hadamard _ _ <- boxes])
       (length [() | HG.Box (Spider _ p) _ _ <- boxes, nonClifford p])

-- Seed 42, eight qubits, one hundred gates. The tuple contains the rewrite
-- count and the original, graph-like, and reduced diagrams in that order.
largeExample :: Either String (Int, SomeDiagram, SomeDiagram, SomeDiagram)
largeExample = do
  gates <- cnotHadPhaseCircuit 8 100 42
  original <- circuitDiagram 8 gates
  case original of
    HG.SomeHypergraph graph -> do
      normal <- normaliseGraphLike graph
      (steps, reduced) <- simplify normal
      normal // reduced // pure (steps, original, HG.SomeHypergraph normal, HG.SomeHypergraph reduced)

-- A T gate next to its inverse, H-H, and an X phase surrounded by H gates.
-- The remaining CNOT puts the cancellations inside a connected two-qubit graph.
before :: QQ ~> QQ
before = (z (1 / 4) ** h) . (z (-(1 / 4)) ** h) . cnot . ((h . x (1 / 4) . h) ** id)

sorts :: Int -> [HG.SomeSort ()]
sorts n = concat (replicate n (HG.sortList @() @'[ '()]))

ports :: HG.Box l n -> [n]
ports (HG.Box _ is os) = is ++ os

-- Every symbolic box is bent into a state. ZX spiders and the Hadamard tensor
-- are symmetric, so this forgets port direction without changing the semantics.
stateBox :: HG.Box l n -> HG.Box l n
stateBox (HG.Box l is os) = HG.Box l [] (is ++ os)

-- Fixed labels and captured port lists form one rule set, compiled once.
-- Captured sequences retain their order; the surrounding captures let a
-- connecting wire occur at any port position on a symmetric spider.
rules :: Either String (R.CompiledRules Int () (Generator Rational))
rules = cleanupRules True

-- Preserve boundary identity paths during elimination cleanup.
structuralCleanup :: Either String (R.CompiledRules Int () (Generator Rational))
structuralCleanup = cleanupRules False

cleanupRules :: Bool -> Either String (R.CompiledRules Int () (Generator Rational))
cleanupRules removeIdentities =
  sequence
    ( hadamardLoops
        ++ parallelEdges
        ++ [r | removeIdentities, r <- identities]
        ++ cancellations
        ++ loops
        ++ fusions
        ++ [colour]
    )
    >>= R.compileRules . zip [0 :: Int ..]
  where
    graph n = R.PortGraph (sorts n)
    alpha = R.Variable "alpha"
    beta = R.Variable "beta"
    -- H(x,x) = (-1)^x / sqrt(2); a parallel pair contributes 1/2.
    hadamardLoops =
      [ R.parameterPortRule
          ( graph
              2
              []
              [HG.Box (Spider Z alpha) [] [R.Capture "a", R.Node 0, R.Capture "b", R.Node 1, R.Capture "c"], HG.Box Hadamard [] hs]
          )
          ( graph
              0
              []
              [ HG.Box (Spider Z (R.mapParameter phase (alpha + 1))) [] [R.Capture "a", R.Capture "b", R.Capture "c"]
              , HG.Box (Scalar (-1) 0) [] []
              ]
          )
      | hs <- [[R.Node 0, R.Node 1], [R.Node 1, R.Node 0]]
      ]
        ++ [R.parameterPortRule (graph 1 [] [HG.Box Hadamard [] [R.Node 0, R.Node 0]]) (graph 0 [] [HG.Box (Spider Z 1) [] []])]
    parallelEdges =
      [ R.parameterPortRule
          ( graph
              4
              []
              [ HG.Box (Spider Z alpha) [] [R.Capture "a", R.Node 0, R.Capture "b", R.Node 2, R.Capture "c"]
              , HG.Box (Spider Z beta) [] [R.Capture "d", otherFirst, R.Capture "e", otherSecond, R.Capture "f"]
              , HG.Box Hadamard [] firstH
              , HG.Box Hadamard [] secondH
              ]
          )
          ( graph
              0
              []
              [ HG.Box (Spider Z alpha) [] [R.Capture "a", R.Capture "b", R.Capture "c"]
              , HG.Box (Spider Z beta) [] [R.Capture "d", R.Capture "e", R.Capture "f"]
              , HG.Box (Scalar (-2) 0) [] []
              ]
          )
      | (otherFirst, otherSecond) <- [(R.Node 1, R.Node 3), (R.Node 3, R.Node 1)]
      , firstH <- [[R.Node 0, R.Node 1], [R.Node 1, R.Node 0]]
      , secondH <- [[R.Node 2, R.Node 3], [R.Node 3, R.Node 2]]
      ]
    identities =
      [ R.parameterPortRule
          (graph 2 [0, 1] [HG.Box (Spider c 0) [] [R.Node 0, R.Node 1]])
          (graph 1 [0, 0] [])
      | c <- [Z, X]
      ]
    cancellations =
      [ R.parameterPortRule
          (graph 3 [0, 2] [HG.Box Hadamard [] a, HG.Box Hadamard [] b])
          (graph 1 [0, 0] [])
      | a <- [[R.Node 0, R.Node 1], [R.Node 1, R.Node 0]]
      , b <- [[R.Node 1, R.Node 2], [R.Node 2, R.Node 1]]
      ]
        ++ [ R.parameterPortRule
               (graph 2 [] [HG.Box Hadamard [] [R.Node 0, R.Node 1], HG.Box Hadamard [] b])
               (graph 1 [] [])
           | b <- [[R.Node 0, R.Node 1], [R.Node 1, R.Node 0]]
           ]
    loops =
      [ R.parameterPortRule
          (graph 1 [] [HG.Box (Spider c alpha) [] [R.Capture "a", R.Node 0, R.Capture "b", R.Node 0, R.Capture "c"]])
          (graph 0 [] [HG.Box (Spider c alpha) [] [R.Capture "a", R.Capture "b", R.Capture "c"]])
      | c <- [Z, X]
      ]
    fusions =
      [ R.parameterPortRule
          ( graph
              1
              []
              [ HG.Box (Spider c alpha) [] [R.Capture "a", R.Node 0, R.Capture "b"]
              , HG.Box (Spider c beta) [] [R.Capture "c", R.Node 0, R.Capture "d"]
              ]
          )
          ( graph
              0
              []
              [ HG.Box
                  (Spider c (R.mapParameter phase (alpha + beta)))
                  []
                  [R.Capture "a", R.Capture "b", R.Capture "c", R.Capture "d"]
              ]
          )
      | c <- [Z, X]
      ]
    colour = R.parameterPortRuleWith
      (graph 0 [] [HG.Box (Spider X alpha) [] [R.Capture "legs"]])
      \sizes ->
        let degree = sizes Map.! "legs"
        in graph
             degree
             []
             ( HG.Box (Spider Z alpha) [] [R.Node i | i <- [0 .. degree - 1]]
                 : [HG.Box Hadamard [] [R.Element "legs" i, R.Node i] | i <- [0 .. degree - 1]]
             )

-- Each step decreases (X spiders, boxes, ports) lexicographically. Colour
-- change can add Hadamards; fusion removes a box and loop removal two ports.
optimise
  :: (a :: Diagram) ~> b -> Either String (Int, HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
optimise graph =
  graph // do
    compiled <- rules
    let (ns, is, os, bs) = HG.hypergraphParts graph
        states = HG.unsafeOpenHypergraph ns is os (map stateBox bs)
        result = R.normalise R.unlimitedRewrites compiled states
    pure (fromIntegral (R.normalisationRewrites result), R.normalisedGraph result)

-- Scalar boxes have no ports, so their product can be collected without
-- changing wiring. Keep the exact power and rational phase, including zero.
collectScalars
  :: (a :: Diagram) ~> b -> HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram)
collectScalars diagram =
  diagram //
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        scalar (HG.Box Scalar{} [] []) = True
        scalar _ = False
        power = sum [k | HG.Box (Scalar k _) [] [] <- boxes]
        angle = phase (sum [a | HG.Box (Scalar _ a) [] [] <- boxes])
    in HG.unsafeOpenHypergraph
         ns
         ins
         outs
         (filter (not . scalar) boxes ++ [HG.Box (Scalar power angle) [] [] | power /= 0 || angle /= 0])

-- Replace implicit Frobenius junctions by explicit Z(0) boxes, assigning a
-- separate wire to every occurrence. Degree-two nodes already are wires.
-- An unused node is a scalar loop of dimension two, not disposable garbage.
materialiseJunctions
  :: (a :: Diagram) ~> b -> HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram)
materialiseJunctions diagram =
  diagram //
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        uses = ins ++ outs ++ concatMap ports boxes
        counts = Map.fromListWith (+) [(n, 1 :: Int) | n <- uses]
        degree n = Map.findWithDefault 0 n counts
        rename next n = if degree n == 2 then (next, n) else (next + 1, next)
        (end, renamed) = mapAccumL rename (length ns) uses
        (inputs, afterInputs) = splitAt (length ins) renamed
        (outputs, afterOutputs) = splitAt (length outs) afterInputs
        rebuild rest (HG.Box l is os) =
          let (is', afterIs) = splitAt (length is) rest
              (os', remaining) = splitAt (length os) afterIs
          in (remaining, HG.Box l is' os')
        (_, originals) = mapAccumL rebuild afterOutputs boxes
        occurrences = Map.fromListWith (++) [(n, [new]) | (n, new) <- zip uses renamed]
        junctions =
          [ if degree n == 0
              then HG.Box (Scalar 2 0) [] []
              else HG.Box (Spider Z 0) [] (Map.findWithDefault [] n occurrences)
          | n <- [0 .. length ns - 1]
          , degree n /= 2
          ]
        kept = [n | n <- [0 .. length ns - 1], degree n == 2] ++ [length ns .. end - 1]
        ids = Map.fromList (zip kept [0 ..])
    in HG.unsafeOpenHypergraph
         (sorts (length kept))
         (map (ids Map.!) inputs)
         (map (ids Map.!) outputs)
         (map (fmap (ids Map.!)) (originals ++ junctions))

-- Insert identities only after cleanup. Each boundary position gets its own
-- Z spider. When a Z spider already has a claimed boundary, an identity path
-- Z(0)-H-Z(0)-H separates the next attachment without introducing plain Z-Z
-- edges. A boundary attached to H or another boundary needs just one Z(0).
repairBoundaries
  :: (a :: Diagram) ~> b -> HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram)
repairBoundaries diagram =
  diagram //
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        repair (next, claimed, bs) wire =
          case find (\(_, box) -> case HG.label box of Spider Z _ -> wire `elem` ports box; _ -> False) (zip [0 :: Int ..] bs) of
            Just (i, _) | IS.notMember i claimed -> ((next, IS.insert i claimed, bs), wire)
            Just _ ->
              (
                ( next + 4
                , IS.insert (length bs) claimed
                , bs
                    ++ [ HG.Box (Spider Z 0) [] [next, next + 1]
                       , HG.Box Hadamard [] [next + 1, next + 2]
                       , HG.Box (Spider Z 0) [] [next + 2, next + 3]
                       , HG.Box Hadamard [] [next + 3, wire]
                       ]
                )
              , next
              )
            Nothing -> ((next + 1, IS.insert (length bs) claimed, bs ++ [HG.Box (Spider Z 0) [] [next, wire]]), next)
        ((end, _, repaired), boundary) = mapAccumL repair (length ns, IS.empty, boxes) (ins ++ outs)
        (inputs, outputs) = splitAt (length ins) boundary
    in HG.unsafeOpenHypergraph (ns ++ sorts (end - length ns)) inputs outputs repaired

-- The normal form is a simple Z/H graph with one distinct boundary spider per
-- input/output position. This intentionally leaves boundary identity paths in
-- place. Sending them back through unrestricted identity elimination would
-- undo the boundary repair. Already graph-like interiors need no cleanup.
normaliseGraphLike
  :: (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
normaliseGraphLike diagram = do
  let (_, _, _, boxes) = HG.hypergraphParts diagram
      valid (HG.Box Spider{} _ _) = True
      valid (HG.Box Hadamard is os) = length (is ++ os) == 2
      valid (HG.Box Scalar{} is os) = null (is ++ os)
      valid _ = False
  unless (all valid boxes) (Left "normaliseGraphLike: invalid ZX generator")
  let explicit = materialiseJunctions diagram
  if graphLike explicit
    then pure (collectScalars explicit)
    else do
      (_, cleaned) <- optimise explicit
      let result = collectScalars (repairBoundaries (materialiseJunctions cleaned))
      unless (graphLike result) (Left "normaliseGraphLike: graph-like invariants were not established")
      pure result

-- The tensor identity for a degree-d Z(s*pi/2) spider expands to a clique
-- of d Z(-s*pi/2) spiders, with an H on each captured leg. With normalised
-- Hadamards its scalar is sqrt(2)^(choose(d,2)-d+1) * exp(i*s*pi/4).
-- Applying this rule once, then ordinary cleanup, fuses phases into neighbours
-- and cancels existing H edges against the inserted ones.
localComplementRules :: Either String (R.CompiledRules Int () (Generator Rational))
localComplementRules = traverse expansion [1, -1] >>= R.compileRules . zip [0 :: Int ..]
  where
    expansion sign = R.parameterPortRuleWith
      (R.PortGraph @() [] [] [HG.Box (Selected (R.Literal (phase (sign / 2)))) [] [R.Capture "legs"]])
      \sizes ->
        let degree = sizes Map.! "legs"
            pairs = [(i, j) | i <- [0 .. degree - 1], j <- [i + 1 .. degree - 1]]
            numbered = zip [0 ..] pairs
            endpoint k side = R.Node (degree + 2 * k + side)
            leg i = R.Node i
            spiderPorts i =
              leg i
                : concat
                  [ [endpoint k 0 | i == a] ++ [endpoint k 1 | i == b]
                  | (k, (a, b)) <- numbered
                  ]
        in R.PortGraph
             (sorts (degree + 2 * length pairs))
             []
             ( HG.Box (Scalar (length pairs - degree + 1) (sign / 4)) [] []
                 : [HG.Box (Spider Z (R.Literal (phase (negate sign / 2)))) [] (spiderPorts i) | i <- [0 .. degree - 1]]
                 ++ [HG.Box Hadamard [] [R.Element "legs" i, leg i] | i <- [0 .. degree - 1]]
                 ++ [HG.Box Hadamard [] [endpoint k 0, endpoint k 1] | (k, _) <- numbered]
             )

-- Fourier expansion of two Pauli spiders joined by H. For m and n external
-- legs, the replacement is a complete bipartite graph with phases b*pi and
-- a*pi on the two sides. Its scalar is sqrt(2)^(m*n-m-n+1) * (-1)^(a*b).
-- Common neighbours become ordinary fusions and Hadamard loops in cleanup.
pivotRules :: Either String (R.CompiledRules Int () (Generator Rational))
pivotRules = pivotExpansion False

-- Moving the right phase onto a leaf retains the parity of the left legs.
-- A k-target gadget contributes sqrt(2)^(1-k), so its scalar correction differs
-- from the Pauli expansion by sqrt(2)^(k-1).
gadgetPivotRules :: Either String (R.CompiledRules Int () (Generator Rational))
gadgetPivotRules = pivotExpansion True

pivotExpansion :: Bool -> Either String (R.CompiledRules Int () (Generator Rational))
pivotExpansion gadget =
  sequence
    [ expansion a b angle hs
    | a <- [0, 1]
    , (b, angle) <- if gadget then [(R.Variable "beta", 0)] else [(R.Literal b, b) | b <- [0, 1]]
    , hs <- [[R.Node 0, R.Node 1], [R.Node 1, R.Node 0]]
    ]
    >>= R.compileRules . zip [0 :: Int ..]
  where
    expansion a b angle hs = R.parameterPortRuleWith
      ( R.PortGraph
          (sorts 2)
          []
          [ HG.Box (Pivot False (R.Literal a)) [] [R.Capture "la", R.Node 0, R.Capture "lb"]
          , HG.Box (Pivot True b) [] [R.Capture "ra", R.Node 1, R.Capture "rb"]
          , HG.Box Hadamard [] hs
          ]
      )
      \sizes ->
        let captured side = [(name, i) | name <- side, i <- [0 .. sizes Map.! name - 1]]
            left = captured ["la", "lb"]
            right = captured ["ra", "rb"]
            m = length left
            n = length right
            pairs = [(i, m + j) | i <- [0 .. m - 1], j <- [0 .. n - 1]]
            numbered = zip [0 ..] pairs
            endpoint k side = R.Node (m + n + 2 * k + side)
            spiderPorts i =
              R.Node i
                : [R.Node (gadgetStart + 2 * i) | gadget, i < m]
                ++ concat
                  [[endpoint k 0 | i == u] ++ [endpoint k 1 | i == v] | (k, (u, v)) <- numbered]
            gadgetStart = m + n + 2 * length pairs
            leafPort = R.Node (gadgetStart + 2 * m)
            rootPort = R.Node (gadgetStart + 2 * m + 1)
            gadgetBoxes =
              [ HG.Box (Spider Z (R.Literal a)) [] (rootPort : [R.Node (gadgetStart + 2 * i + 1) | i <- [0 .. m - 1]])
              , HG.Box (Spider Z b) [] [leafPort]
              , HG.Box Hadamard [] [rootPort, leafPort]
              ]
                ++ [HG.Box Hadamard [] [R.Node (gadgetStart + 2 * i), R.Node (gadgetStart + 2 * i + 1)] | i <- [0 .. m - 1]]
        in R.PortGraph
             (sorts (gadgetStart + if gadget then 2 * m + 2 else 0))
             []
             ( HG.Box (Scalar (m * n - m - n + if gadget then m else 1) (a * angle)) [] []
                 : [ HG.Box (Spider Z (if i < m then (if gadget then R.Literal 0 else b) else R.Literal a)) [] (spiderPorts i)
                   | i <- [0 .. m + n - 1]
                   ]
                 ++ [HG.Box Hadamard [] [R.Element name j, R.Node i] | (i, (name, j)) <- zip [0 ..] (left ++ right)]
                 ++ [HG.Box Hadamard [] [endpoint k 0, endpoint k 1] | (k, _) <- numbered]
                 ++ [box | gadget, box <- gadgetBoxes]
             )

-- An open graph encoded as explicit Z spiders and Hadamard boxes. Each graph
-- edge gets two distinct wire nodes, one at each end of its Hadamard box.
-- The first vertices have output wires. The remaining vertices are internal.
openGraph :: Int -> [Rational] -> [(Int, Int)] -> SomeDiagram
openGraph boundary phases edges =
  let endpoint k side = boundary + 2 * k + side
      incident i = concat [[endpoint k 0 | i == a] ++ [endpoint k 1 | i == b] | (k, (a, b)) <- zip [0 ..] edges]
      boxes =
        [HG.Box (Spider Z (phase p)) [] ([i | i < boundary] ++ incident i) | (i, p) <- zip [0 ..] phases]
          ++ [HG.Box Hadamard [] [endpoint k 0, endpoint k 1] | k <- [0 .. length edges - 1]]
  in HG.reifySorts (sorts boundary) \ @bs ->
       HG.SomeHypergraph
         (HG.unsafeOpenHypergraph @_ @'[] @bs (sorts (boundary + 2 * length edges)) [] [0 .. boundary - 1] boxes)

-- Check graph-like interiors, direct Z boundary attachments, simple H edges,
-- and at most one boundary attachment per spider. Isolated wires and zero-leg
-- spiders/scalar boxes are allowed scalar components.
graphLike :: (a :: Diagram) ~> b -> Bool
graphLike diagram = validLabels && validWires && simpleEdges && validBoundaries
  where
    (ns, ins, outs, boxes) = HG.hypergraphParts diagram
    numbered = zip [0 :: Int ..] boxes
    boundary = ins ++ outs
    incidences =
      Map.fromListWith
        (++)
        ( [(n, [(-1, i)]) | (i, n) <- zip [0 ..] boundary]
            ++ [(n, [(kind l, i)]) | (i, HG.Box l is os) <- numbered, n <- is ++ os]
        )
    kind :: Generator a -> Int
    kind Spider{} = 0
    kind Hadamard = 1
    kind _ = 2
    validLabels = all valid boxes
    valid (HG.Box (Spider Z _) _ _) = True
    valid (HG.Box Hadamard is os) = length (is ++ os) == 2
    valid (HG.Box Scalar{} is os) = null (is ++ os)
    valid _ = False
    at n = Map.findWithDefault [] n incidences
    validWires =
      all
        ( \n -> case at n of
            [] -> True
            [(a, _), (b, _)] -> (a == 0 && b == 1) || (a == 1 && b == 0) || (a == -1 && b == 0) || (a == 0 && b == -1)
            _ -> False
        )
        [0 .. length ns - 1]
    neighbours n = [i | (0, i) <- at n]
    edgePairs =
      [ pair
      | (_, HG.Box Hadamard is os) <- numbered
      , let endpoints = concatMap neighbours (is ++ os)
      , pair <- case endpoints of [a, b] -> [(min a b, max a b)]; _ -> []
      ]
    simpleEdges =
      length edgePairs == length [() | HG.Box Hadamard _ _ <- boxes]
        && all (uncurry (/=)) edgePairs
        && length edgePairs == length (nubOrd edgePairs)
    boundarySpiders = concatMap neighbours boundary
    validBoundaries = length boundarySpiders == length boundary && length boundarySpiders == length (nubOrd boundarySpiders)

-- Box indices of eligible internal spiders, in their existing occurrence order.
-- Zero-leg spiders are scalar components and can also be expanded exactly.
localComplementCandidates :: (a :: Diagram) ~> b -> [Int]
localComplementCandidates diagram =
  let (_, ins, outs, boxes) = HG.hypergraphParts diagram
      boundary = IS.fromList (ins ++ outs)
  in [ i
     | (i, HG.Box (Spider Z p) is os) <- zip [0 ..] boxes
     , phase p `elem` [1 / 2, 3 / 2]
     , all (`IS.notMember` boundary) (is ++ os)
     ]

-- Each H edge whose endpoints are distinct internal Pauli spiders is eligible.
-- Occurrence indices remain stable until the selected expansion is applied.
pivotCandidates :: (a :: Diagram) ~> b -> [(Int, Int)]
pivotCandidates diagram =
  let (_, ins, outs, boxes) = HG.hypergraphParts diagram
      boundary = IS.fromList (ins ++ outs)
      spiders =
        Map.fromList
          [ (wire, i)
          | (i, box@(HG.Box (Spider Z p) _ _)) <- zip [0 ..] boxes
          , phase p `elem` [0, 1]
          , all (`IS.notMember` boundary) (ports box)
          , wire <- ports box
          ]
  in nubOrd
       [ (min i j, max i j)
       | box@(HG.Box Hadamard _ _) <- boxes
       , [a, b] <- [ports box]
       , Just i <- [Map.lookup a spiders]
       , Just j <- [Map.lookup b spiders]
       , i /= j
       ]

-- The adjacency index uses spider occurrences, not their wire-node numbers.
-- This is also the canonical key for unordered phase-gadget target sets.
data ZXGraph = ZXGraph
  { zPhases :: Map.Map Int Rational
  , zNeighbours :: Map.Map Int [(Int, Int)]
  , zBoundary :: IS.IntSet
  , zBoundaryPositions :: [(Int, Int)]
  }

zxGraph :: (a :: Diagram) ~> b -> ZXGraph
zxGraph diagram =
  let (_, ins, outs, boxes) = HG.hypergraphParts diagram
      spiders = [(i, phase p, ports box) | (i, box@(HG.Box (Spider Z p) _ _)) <- zip [0 ..] boxes]
      wires = Map.fromList [(wire, i) | (i, _, ps) <- spiders, wire <- ps]
      boundary = [(i, position) | (position, wire) <- zip [0 ..] (ins ++ outs), Just i <- [Map.lookup wire wires]]
      edges =
        [ (i, a, b)
        | (i, box@(HG.Box Hadamard _ _)) <- zip [0 ..] boxes
        , [u, v] <- [ports box]
        , Just a <- [Map.lookup u wires]
        , Just b <- [Map.lookup v wires]
        ]
  in ZXGraph
       (Map.fromList [(i, p) | (i, p, _) <- spiders])
       (Map.fromListWith (++) (concat [[(a, [(edge, b)]), (b, [(edge, a)])] | (edge, a, b) <- edges]))
       (IS.fromList (map fst boundary))
       boundary

nonClifford :: Rational -> Bool
nonClifford p = denominator (2 * phase p) /= 1

adjacent :: ZXGraph -> Int -> [Int]
adjacent view i = map snd (Map.findWithDefault [] i (zNeighbours view))

internal :: ZXGraph -> Int -> Bool
internal view i = IS.notMember i (zBoundary view)

data Gadget = Gadget {gadgetRoot :: Int, gadgetLeaf :: Int, gadgetTargets :: [Int]}
  deriving (Eq, Show)

phaseGadgets :: ZXGraph -> [Gadget]
phaseGadgets view =
  Map.elems
    ( Map.fromListWith
        (\_ old -> old)
        [ (root, Gadget root leaf (IS.toAscList (IS.fromList (filter (/= leaf) (adjacent view root)))))
        | (leaf, p) <- Map.toAscList (zPhases view)
        , nonClifford p
        , internal view leaf
        , [root] <- [adjacent view leaf]
        , internal view root
        , Just q <- [Map.lookup root (zPhases view)]
        , q `elem` [0, 1]
        ]
    )

gadgetPivotCandidates :: (a :: Diagram) ~> b -> [(Int, Int)]
gadgetPivotCandidates diagram =
  let view = zxGraph diagram
      leaf i = internal view i && length (adjacent view i) == 1
  in [ (a, b)
     | (a, p) <- Map.toAscList (zPhases view)
     , p `elem` [0, 1]
     , internal view a
     , b <- nubOrd (adjacent view a)
     , internal view b
     , Just q <- [Map.lookup b (zPhases view)]
     , nonClifford q
     , not (leaf b)
     , not (any leaf (filter (/= b) (adjacent view a)))
     ]

-- A direct boundary Z(0) with one H neighbour is identity padding. Both
-- it and the spider behind that H belong to the same boundary position for
-- pivot selection. Multiple positions remain distinct, including input/output
-- positions sharing a neighbour. No graph labels or boundary wires change.
boundaryAttachments :: (a :: Diagram) ~> b -> Map.Map Int [Int]
boundaryAttachments = indexedBoundaryAttachments . zxGraph

indexedBoundaryAttachments :: ZXGraph -> Map.Map Int [Int]
indexedBoundaryAttachments view =
  let direct = zBoundaryPositions view
      padded = [(other, position) | (i, position) <- direct, zPhases view Map.! i == 0, [other] <- [adjacent view i]]
  in Map.fromListWith (++) [(i, [position]) | (i, position) <- direct ++ padded]

boundaryPivotCandidates :: (a :: Diagram) ~> b -> [(Int, Int)]
boundaryPivotCandidates diagram =
  let view = zxGraph diagram
      attachments = indexedBoundaryAttachments view
      leaf i = internal view i && length (adjacent view i) == 1
  in [ (a, b)
     | (a, p) <- Map.toAscList (zPhases view)
     , p `elem` [0, 1]
     , Map.notMember a attachments
     , not (any leaf (adjacent view a))
     , b <- IS.toAscList (IS.fromList (adjacent view a))
     , Just [_] <- [Map.lookup b attachments]
     ]

-- Boundary rounds are compared after interior simplification. Ignoring
-- boundary padding and phase-gadget bodies lets a pivot remove an interior
-- Pauli spider even when its replacement adds an identity or a phase gadget.
interiorSize :: (a :: Diagram) ~> b -> Int
interiorSize diagram =
  let view = zxGraph diagram
      attachments = indexedBoundaryAttachments view
      gadgets = IS.fromList (concat [[gadgetRoot g, gadgetLeaf g] | g <- phaseGadgets view])
  in length [() | i <- Map.keys (zPhases view), Map.notMember i attachments, IS.notMember i gadgets]

-- Extraction leaves the spider count unchanged but turns a non-Clifford phase
-- into a gadget leaf. Normalisation clears a Pauli root phase. Other steps
-- remove spiders. This lexicographic measure prevents extraction/pivot cycles.
simplificationMeasure :: (a :: Diagram) ~> b -> (Int, Int, Int)
simplificationMeasure diagram =
  let view = zxGraph diagram
      gadgets = phaseGadgets view
  in ( spiderCount diagram
     , length (filter nonClifford (Map.elems (zPhases view))) - length gadgets
     , length [() | g <- gadgets, zPhases view Map.! gadgetRoot g == 1]
     )

spiderCount :: (a :: Diagram) ~> b -> Int
spiderCount diagram = let (_, _, _, boxes) = HG.hypergraphParts diagram in length [() | HG.Box Spider{} _ _ <- boxes]

-- Each accepted boundary round strictly reduces interiorSize. Interior steps
-- use their own lexicographic measure. A trial that only moves padding is
-- discarded, so its new boundary cannot initiate a reverse-pivot cycle.
simplify
  :: (a :: Diagram) ~> b
  -> Either String (Int, HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
simplify diagram = do
  (steps, current) <- simplifyInterior diagram
  go steps current
  where
    go steps current = do
      next <- boundaryReduction current
      case next of
        Nothing -> pure (steps, current)
        Just (count, result) -> go (steps + count) result

-- Prefer local complementation, then internal Pauli pivots, gadget fusion and
-- extraction. Every iteration decreases simplificationMeasure.
simplifyInterior
  :: (a :: Diagram) ~> b
  -> Either String (Int, HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
simplifyInterior diagram = normaliseGraphLike diagram >>= go 0
  where
    go steps current = case localComplementCandidates current of
      i : _ -> advance steps current (localComplementAt i current)
      [] -> case pivotCandidates current of
        pair : _ -> advance steps current (pivotAt pair current)
        [] -> case gadgetReduction current of
          Just result -> advance steps current result
          Nothing -> case gadgetPivotCandidates current of
            pair : _ -> advance steps current (gadgetPivotAt pair current)
            [] -> pure (steps, current)
    advance steps current result = do
      next <- result
      unless
        (simplificationMeasure next < simplificationMeasure current)
        (Left "simplify: step did not decrease the termination measure")
      go (steps + 1) next

-- Starting from an interior fixed point, try candidates until a complete
-- boundary round improves the diagram.
-- Rejected trials are pure: neither their graph nor their step count escapes.
boundaryReduction
  :: (a :: Diagram) ~> b
  -> Either String (Maybe (Int, HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram)))
boundaryReduction current = try (boundaryPivotCandidates current)
  where
    try [] = pure Nothing
    try (pair : rest) = do
      pivoted <- boundaryPivotAt pair current
      (steps, next) <- simplifyInterior pivoted
      if interiorSize next < interiorSize current
        then pure (Just (steps + 1, next))
        else try rest

-- Perform one selected local complementation. The marker restricts expansion
-- to that spider; helper spiders are only consumed by cleanup. Identity
-- elimination is excluded so boundary spiders remain attached throughout.
localComplementAt
  :: Int
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
localComplementAt index diagram =
  diagram // do
    unless (graphLike diagram) (Left "localComplementAt: expected a graph-like diagram")
    unless
      (index `elem` localComplementCandidates diagram)
      (Left "localComplementAt: expected an internal Z spider with phase +/-pi/2")
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        mark i (HG.Box (Spider Z p) is os)
          | i == index = HG.Box (Selected (phase p)) is os
        mark _ box = box
    compiled <- localComplementRules
    eliminate
      "localComplementAt"
      compiled
      (HG.unsafeOpenHypergraph ns ins outs (zipWith (\i -> stateBox . mark i) [0 ..] boxes))

pivotAt
  :: (Int, Int)
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
pivotAt pair@(left, right) diagram =
  diagram // do
    unless (graphLike diagram) (Left "pivotAt: expected a graph-like diagram")
    unless
      (pair `elem` pivotCandidates diagram)
      (Left "pivotAt: expected an ordered pair of adjacent internal Pauli spiders")
    compiled <- pivotRules
    markedPivot "pivotAt" compiled (left, right) diagram

gadgetPivotAt
  :: (Int, Int)
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
gadgetPivotAt pair diagram = do
  unless (graphLike diagram) (Left "gadgetPivotAt: expected a graph-like diagram")
  unless
    (pair `elem` gadgetPivotCandidates diagram)
    (Left "gadgetPivotAt: expected an internal Pauli/non-Clifford pair outside existing gadgets")
  compiled <- gadgetPivotRules
  markedPivot "gadgetPivotAt" compiled pair diagram

-- The same tensor expansion works when the right endpoint has a boundary.
-- Pauli phases use ordinary pivoting; other phases are retained in a gadget.
-- Cleanup cancels existing H edges, then restores direct Z boundary attachments.
boundaryPivotAt
  :: (Int, Int)
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
boundaryPivotAt pair@(_, right) diagram = do
  unless (graphLike diagram) (Left "boundaryPivotAt: expected a graph-like diagram")
  unless
    (pair `elem` boundaryPivotCandidates diagram)
    (Left "boundaryPivotAt: expected an interior Pauli spider beside one boundary position")
  let p = zPhases (zxGraph diagram) Map.! right
  compiled <- if p `elem` [0, 1] then pivotRules else gadgetPivotRules
  markedPivot "boundaryPivotAt" compiled pair diagram

markedPivot
  :: String
  -> R.CompiledRules Int () (Generator Rational)
  -> (Int, Int)
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
markedPivot name compiled (left, right) diagram =
  diagram //
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        mark i (HG.Box (Spider Z p) is os)
          | i == left = HG.Box (Pivot False (phase p)) is os
          | i == right = HG.Box (Pivot True (phase p)) is os
        mark _ box = box
    in eliminate name compiled (HG.unsafeOpenHypergraph ns ins outs (zipWith (\i -> stateBox . mark i) [0 ..] boxes))

-- Pivot congruence retains arbitrary endpoint phases by unfusing them before
-- applying the existing zero-phase pivot expansion. Boundary wires move to
-- the phase spiders, so every external position stays directly on a Z spider.
-- This is the pivot congruence used by PyZX's local-search strategies.
pivotCongruenceAt
  :: (Int, Int)
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
pivotCongruenceAt (left, right) diagram =
  diagram // do
    unless (graphLike diagram) (Left "pivotCongruenceAt: expected graph-like form")
    unless
      (left < right && right `elem` adjacent (zxGraph diagram) left)
      (Left "pivotCongruenceAt: expected an ordered adjacent pair")
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        boundary = IS.fromList (ins ++ outs)
        chosen = Map.fromList [(left, (False, length ns)), (right, (True, length ns + 1))]
        core i box = case Map.lookup i chosen of
          Nothing -> stateBox box
          Just (side, wire) -> HG.Box (Pivot side 0) [] (wire : filter (`IS.notMember` boundary) (ports box))
        leaves =
          [ HG.Box (Spider Z (phase p)) [] (wire : filter (`IS.member` boundary) (ports box))
          | (i, box@(HG.Box (Spider Z p) _ _)) <- zip [0 ..] boxes
          , Just (_, wire) <- [Map.lookup i chosen]
          ]
        host = HG.unsafeOpenHypergraph (ns ++ sorts 2) ins outs (zipWith core [0 ..] boxes ++ leaves)
    compiled <- pivotRules
    eliminate "pivotCongruenceAt" compiled host

-- The three disjoint neighbourhood sets give the edges toggled by a pivot.
-- Two phase spiders and two H edges are added. Counting existing edges avoids
-- constructing any replacement for candidates that cannot lower the score.
pivotCongruenceDelta :: ZXGraph -> (Int, Int) -> Int
pivotCongruenceDelta view (left, right) =
  let a = IS.delete right (IS.fromList (adjacent view left))
      b = IS.delete left (IS.fromList (adjacent view right))
      common = IS.intersection a b
      onlyA = IS.difference a common
      onlyB = IS.difference b common
      pairs = [(i, j) | (xs, ys) <- [(onlyA, onlyB), (onlyA, common), (onlyB, common)], i <- IS.toList xs, j <- IS.toList ys]
      existing = length [() | (i, j) <- pairs, j `elem` adjacent view i]
  in length pairs - 2 * existing + 4

-- Greedy local search over exact pivot congruences. Run after simplify: its
-- spider-elimination rules can undo congruences that save H edges. Each move
-- strictly lowers spiders+H edges, so this search terminates and is idempotent.
reduceEdges
  :: (a :: Diagram) ~> b
  -> Either String (Int, HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
reduceEdges diagram = normaliseGraphLike diagram >>= go 0
  where
    size graph = let DiagramSize spiders hs _ = diagramSize graph in spiders + hs
    go steps current =
      let view = zxGraph current
          candidates =
            [ (delta, (i, j))
            | (i, ns) <- Map.toAscList (zNeighbours view)
            , (_, j) <- ns
            , i < j
            , let delta = pivotCongruenceDelta view (i, j)
            , delta < 0
            ]
      in case candidates of
           [] -> pure (steps, current)
           first : rest -> do
             let (_, pair) = foldl' min first rest
             next <- pivotCongruenceAt pair current
             unless (size next < size current) (Left "reduceEdges: pivot did not lower the graph size")
             go (steps + 1) next

furtherExample :: Either String (Int, SomeDiagram)
furtherExample = do
  (_, _, _, HG.SomeHypergraph graph) <- largeExample
  (steps, result) <- reduceEdges graph
  result // pure (steps, HG.SomeHypergraph result)

-- A set index finds equal supports. Only this ZX-specific selection is outside
-- the generic matcher: the selected fragments are replaced by a literal rule,
-- with the engine checking gluing, dangling wires and replacement interfaces.
gadgetReduction
  :: (a :: Diagram) ~> b
  -> Maybe (Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram)))
gadgetReduction diagram =
  let view = zxGraph diagram
      gadgets = phaseGadgets view
      groups = Map.elems (Map.fromListWith (++) [(gadgetTargets g, [g]) | g <- gadgets])
      choices =
        [[g] | g <- gadgets, length (gadgetTargets g) <= 1]
          ++ [gs | gs <- groups, length gs > 1]
          ++ [[g] | g <- gadgets, zPhases view Map.! gadgetRoot g == 1]
  in case choices of
       [] -> Nothing
       gs : _ -> Just (reduceGadgets view gs diagram)

reduceGadgets
  :: ZXGraph
  -> [Gadget]
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
reduceGadgets _ [] _ = Left "reduceGadgets: empty group"
reduceGadgets view gs@(first : _) diagram =
  let targets = gadgetTargets first
      size = length targets
      value g =
        let root = zPhases view Map.! gadgetRoot g; leaf = zPhases view Map.! gadgetLeaf g
        in ((1 - 2 * root) * leaf, root * leaf)
      total = phase (sum (map (fst . value) gs))
      angle = phase (sum (map (snd . value) gs))
      removedGadgets = if size <= 1 then gs else drop 1 gs
      removedSpiders = IS.fromList (concat [[gadgetRoot g, gadgetLeaf g] | g <- removedGadgets])
      removedEdges = IS.fromList [e | i <- IS.toList removedSpiders, (e, _) <- Map.findWithDefault [] i (zNeighbours view)]
      connectorEdges = IS.fromList [e | g <- gs, (e, _) <- Map.findWithDefault [] (gadgetRoot g) (zNeighbours view)]
      removed = IS.union removedSpiders removedEdges
      (_, _, _, boxes) = HG.hypergraphParts diagram
      cutWires = IS.fromList [wire | (i, box) <- zip [0 ..] boxes, IS.member i removedEdges, wire <- ports box]
      changed = IS.fromList ((if IS.null removed then [] else targets) ++ [i | size > 1, i <- [gadgetRoot first, gadgetLeaf first]])
      change i (HG.Box (Spider Z p) is os) =
        let q
              | size > 1 && i == gadgetRoot first = 0
              | size > 1 && i == gadgetLeaf first = total
              | size == 1 = phase (p + total)
              | otherwise = p
        in HG.Box (Spider Z q) (filter (`IS.notMember` cutWires) is) (filter (`IS.notMember` cutWires) os)
      change _ box = box
      power = if size == 0 then 1 else (1 - size) * (length gs - 1)
      rhs =
        [ change i box
        | (i, box) <- zip [0 ..] boxes
        , IS.member i changed || (IS.member i connectorEdges && IS.notMember i removedEdges)
        ]
          ++ [HG.Box (Scalar power angle) [] [] | power /= 0 || angle /= 0]
  in replaceFragment (IS.fromList (map gadgetLeaf gs)) (IS.unions [removed, changed, connectorEdges]) rhs diagram

replaceFragment
  :: IS.IntSet
  -> IS.IntSet
  -> [HG.Box (Generator Rational) Int]
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
replaceFragment marked selected rhs diagram =
  diagram // do
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
        mark i (HG.Box (Spider Z p) is os) | IS.member i marked = HG.Box (Selected p) is os
        mark _ box = box
        hostBoxes = zipWith mark [0 ..] boxes
        lhs = [box | (i, box) <- zip [0 ..] hostBoxes, IS.member i selected]
        outside = IS.fromList (ins ++ outs ++ [wire | (i, box) <- zip [0 ..] boxes, IS.notMember i selected, wire <- ports box])
        interface = IS.toAscList (IS.intersection outside (IS.fromList (concatMap ports lhs)))
        fragment bs =
          let nodes = nubOrd (interface ++ concatMap ports bs)
              ids = Map.fromList (zip nodes [0 ..])
          in R.PortGraph (sorts (length nodes)) (map (ids Map.!) interface) (map (fmap (R.Node . (ids Map.!)) . stateBox) bs)
    rule <- R.portRule (fragment lhs) (fragment rhs)
    compiled <- R.compileRules [(0 :: Int, rule)]
    eliminate "gadgetReduction" compiled (HG.unsafeOpenHypergraph ns ins outs (map stateBox hostBoxes))

eliminate
  :: String
  -> R.CompiledRules Int () (Generator Rational)
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
eliminate name compiled host = case R.rewritesCompiled compiled host of
  [(_, expanded)] -> do
    cleanup <- structuralCleanup
    let cleaned = R.normalisedGraph (R.normalise R.unlimitedRewrites cleanup expanded)
        result = collectScalars (repairBoundaries (materialiseJunctions cleaned))
    unless (graphLike result) (Left (name ++ ": cleanup did not restore graph-like form"))
    pure result
  _ -> Left (name ++ ": expansion did not select exactly one match")

-- Interpret explicit spiders using the existing matrix ZX category. The
-- read-back contracts the tensors, including closed components and scalars.
-- A degree-n spider is a phase state followed by n-legged copying in its basis.
spiderTensor :: Colour -> Rational -> Int -> HG.SomeArrow Nat
spiderTensor c p n = fanout n \ys f ->
  HG.SomeArrow Nil ys (f . Str (case c of Z -> ZX.zSpider (pi * fromRational p); X -> ZX.xSpider (pi * fromRational p)))
  where
    fanout :: Int -> (forall ys. (HG.SortList ys) => HG.Sorts ys -> ('[1] ~> ys) -> r) -> r
    fanout 0 k = k Nil (Str (case c of Z -> ZX.zSpider 0; X -> ZX.xSpider 0))
    fanout degree k = fanout (degree - 1) \ys f ->
      withKnownListOf ys $
        k (Cons @1 ys) ((obj @'[1] ** f) . Str (case c of Z -> ZX.zCopy; X -> ZX.xCopy))

matrix :: (a :: Diagram) ~> b -> Either String (Map.Map (Int, Int) (Complex Double))
matrix graph =
  let (ns, is, os, bs) = HG.hypergraphParts graph
      qubits n = concat (replicate n (HG.sortList @Nat @'[1]))
      primitive (HG.Box l ins outs) = HG.Box (HG.unsafePrim (tensor l (length ins + length outs))) [] (ins ++ outs)
      tensor Hadamard _ = HG.someArrow @'[] @'[1, 1] (Str ((obj @1 ** ZX.hadamard @1) . ZX.zSpider 0))
      tensor (Spider c p) n = spiderTensor c p n
      tensor (Selected p) n = spiderTensor Z p n
      tensor (Pivot _ p) n = spiderTensor Z p n
      tensor (Scalar power angle) _ =
        HG.someArrow @'[] @'[]
          (Str (ZX.ZX (Map.singleton (0, 0) (mkPolar (sqrt 2 ^^ power) (pi * fromRational angle))) :: ZX.ZX 0 0))
  in HG.reifySorts (qubits (length is)) \ @as ->
       HG.reifySorts (qubits (length os)) \ @bs -> do
         arrow <-
           HG.simplify
             (HG.frobeniusWith (const 2))
             (HG.unsafeOpenHypergraph @_ @as @bs (qubits (length ns)) is os (map primitive bs))
         pure (matrixEntries (unStr arrow))

boxCount :: (a :: Diagram) ~> b -> Int
boxCount graph = let (_, _, _, bs) = HG.hypergraphParts graph in length bs

-- In graph-like form each H box is drawn as one blue edge between spiders.
-- Other diagrams retain explicit generators and incidence wires.
dot :: String -> (a :: Diagram) ~> b -> String
dot title graph
  | graphLike graph = graphLikeDot title graph
  | otherwise = incidenceDot title graph

graphLikeDot :: String -> (a :: Diagram) ~> b -> String
graphLikeDot title graph =
  let (_, ins, _, _) = HG.hypergraphParts graph
      view = zxGraph graph
      node i = "v" ++ show i
      boundary =
        [ (name ++ show j, name ++ " " ++ show j, i)
        | (i, position) <- zBoundaryPositions view
        , let (name, j) = if position < length ins then ("in", position) else ("out", position - length ins)
        ]
      (power, angle) = scalarFactors (materialiseJunctions graph)
  in unlines $
       [ "graph ZX {"
       , "layout=neato; overlap=false; splines=true; start=42; bgcolor=white;"
       , "label=" ++ quoted (title ++ "\nBlue edges are Hadamards") ++ "; labelloc=t; fontname=Helvetica;"
       , "node [fontname=Helvetica,fontsize=11,shape=circle,style=filled,fillcolor=\"#86efac\",width=0.4];"
       ]
         ++ [node i ++ " [label=" ++ quoted (phaseLabel p) ++ "];" | (i, p) <- Map.toAscList (zPhases view)]
         ++ [ node i ++ " -- " ++ node j ++ " [color=\"#0099ff\",penwidth=1.4];"
            | (i, ns) <- Map.toAscList (zNeighbours view)
            , (_, j) <- ns
            , i < j
            ]
         ++ concat
           [ [name ++ " [shape=plaintext,style=\"\",label=" ++ quoted label ++ "];", name ++ " -- " ++ node i ++ ";"]
           | (name, label, i) <- boundary
           ]
         ++ [ "scalar [shape=box,fillcolor=\"#e5e7eb\",label="
                ++ quoted ("√2^" ++ show power ++ if angle == 0 then "" else " exp(" ++ phaseLabel angle ++ " i)")
                ++ "];"
            | power /= 0 || angle /= 0
            ]
         ++ ["}"]

-- Graphviz displays the actual incidence graph; box port directions are omitted.
incidenceDot :: String -> (a :: Diagram) ~> b -> String
incidenceDot title graph =
  unlines $
    [ "digraph ZX {"
    , if null is
        then "layout=neato; overlap=false; splines=true; start=42; bgcolor=white;"
        else "rankdir=LR; bgcolor=white; nodesep=0.3; ranksep=0.35;"
    , "label=" ++ quoted title ++ "; labelloc=t; fontname=Helvetica;"
    , "node [fontname=Helvetica,fontsize=11]; edge [dir=none];"
    ]
      ++ ["n" ++ show n ++ " [shape=point,width=0.025];" | n <- [0 .. length ns - 1]]
      ++ [name ++ " [shape=plaintext,label=" ++ quoted label ++ "];" | (name, label) <- boundaries]
      ++ [box j b | (j, b) <- zip [0 :: Int ..] bs]
      ++ ["{rank=same; " ++ unwords (map (++ ";") names) ++ "}" | names <- Map.elems ranks]
      ++ [if distance a <= distance b then edge a b else edge b a | (a, b) <- edges]
      ++ ["}"]
  where
    (ns, is, os, bs) = HG.hypergraphParts graph
    boundaries =
      [ (name ++ show j, name ++ " " ++ show j) | (name, nodes) <- [("in", is), ("out", os)], (j, _) <- zip [0 :: Int ..] nodes
      ]
    edges =
      [(name ++ show j, "n" ++ show n) | (name, nodes) <- [("in", is), ("out", os)], (j, n) <- zip [0 :: Int ..] nodes]
        ++ [("b" ++ show j, "n" ++ show n) | (j, b) <- zip [0 :: Int ..] bs, n <- ports b]
    neighbours = Map.fromListWith (++) (concat [[(a, [b]), (b, [a])] | (a, b) <- edges])
    levels = visit 0 ["in" ++ show j | j <- [0 .. length is - 1]] Map.empty
    visit :: Int -> [String] -> Map.Map String Int -> Map.Map String Int
    visit _ [] seen = seen
    visit depth frontier seen =
      let fresh = nubOrd (filter (`Map.notMember` seen) frontier)
          next = concatMap (\v -> Map.findWithDefault [] v neighbours) fresh
      in if null fresh then seen else visit (depth + 1) next (Map.union seen (Map.fromList [(v, depth) | v <- fresh]))
    final = 1 + maximum (0 : Map.elems levels)
    distance v = if take 3 v == "out" then final else Map.findWithDefault 0 v levels
    ranks = Map.fromListWith (++) [(distance v, [v]) | v <- Map.keys neighbours]
    edge a b = a ++ " -> " ++ b ++ ";"
    box j (HG.Box l _ _) =
      let (label, colour, shape) = case l of
            Hadamard -> ("H", "#fde68a", "square")
            Scalar power angle -> ("√2^" ++ show power ++ if angle == 0 then "" else " exp(" ++ phaseLabel angle ++ " i)", "#e5e7eb", "box")
            Selected p -> (phaseLabel p, "#fde68a", "circle")
            Pivot _ p -> (phaseLabel p, "#fde68a", "circle")
            Spider c p -> (phaseLabel p, case c of Z -> "#86efac"; X -> "#fca5a5", "circle")
      in "b"
           ++ show j
           ++ " [shape="
           ++ shape
           ++ ",width=0.4,height=0.4,margin=0.02,style=filled,fillcolor="
           ++ quoted colour
           ++ ",label="
           ++ quoted label
           ++ "];"
phaseLabel :: Rational -> String
phaseLabel 0 = ""
phaseLabel p =
  (if numerator p == 1 then "" else if numerator p == -1 then "-" else show (numerator p))
    ++ "π"
    ++ if denominator p == 1 then "" else "/" ++ show (denominator p)
quoted :: String -> String
quoted text = "\"" ++ concatMap escape text ++ "\""
escape :: Char -> String
escape '\\' = "\\\\"
escape '\"' = "\\\""
escape '\n' = "\\n"
escape c = [c]

pictures :: Either String [(FilePath, String)]
pictures = do
  (steps, after) <- optimise before
  normal <- normaliseGraphLike before
  local <- case openGraph 3 [0, 1 / 4, 0, 1 / 2] [(3, 0), (3, 1), (3, 2), (0, 1)] of
    HG.SomeHypergraph graph -> do
      complemented <- localComplementAt 3 graph
      pure
        [ ("local-before.dot", dot "Before local complementation" graph)
        , ("local-after.dot", dot "After: centre removed, neighbour edges toggled" complemented)
        ]
  automatic <- case automaticExample of
    HG.SomeHypergraph graph -> do
      (count, simplified) <- simplify graph
      pure
        [ ("automatic-before.dot", dot "Before automatic local complementation" graph)
        , ("automatic-after.dot", dot ("After " ++ show count ++ " local complementations") simplified)
        ]
  gadgets <- case gadgetExample of
    HG.SomeHypergraph graph -> do
      (count, simplified) <- simplify graph
      pure
        [ ("gadget-before.dot", dot "Before: two opposite parity phases" graph)
        , ("gadget-after.dot", dot ("After gadget extraction and cancellation: " ++ show count ++ " steps") simplified)
        ]
  boundary <- case boundaryExample of
    HG.SomeHypergraph graph -> do
      (count, simplified) <- simplify graph
      pure
        [ ("boundary-before.dot", dot "Before: an interior Pauli beside a boundary Clifford" graph)
        , ("boundary-after.dot", dot ("After boundary pivot and Clifford cleanup: " ++ show count ++ " steps") simplified)
        ]
  generated <- do
    (count, original, normalised, reduced) <- largeExample
    pure
      [ (name, dot (title ++ " | " ++ sizeLabel graph) graph)
      | (name, title, HG.SomeHypergraph graph) <-
          [ ("generated-before.dot", "8 qubits, 100 gates, seed 42", original)
          , ("generated-graph-like.dot", "Graph-like form", normalised)
          , ("generated-after.dot", "Simplified in " ++ show count ++ " steps", reduced)
          ]
      ]
  further <- do
    (count, HG.SomeHypergraph graph) <- furtherExample
    pure
      [
        ( "generated-further.dot"
        , dot
            ( "Edge reduction | accepted pivots: "
                ++ show count
                ++ " | "
                ++ sizeLabel graph
            )
            graph
        )
      ]
  pure
    ( [ ("before.dot", dot ("Before: " ++ show (boxCount before) ++ " generators") before)
      , ("after.dot", dot ("After: " ++ show (boxCount after) ++ " generators, " ++ show steps ++ " rewrites") after)
      , ("graph-like.dot", dot "Graph-like form with distinct boundary spiders" normal)
      ]
        ++ local
        ++ automatic
        ++ gadgets
        ++ boundary
        ++ generated
        ++ further
    )
  where
    sizeLabel graph =
      let DiagramSize spiders hs phases = diagramSize graph
      in show spiders ++ " spiders, " ++ show hs ++ " H, " ++ show phases ++ " non-Clifford phases"

-- A state with two spiders joined by one or more wires. External legs are
-- deliberately ordered differently on the two spiders.
fusionExample :: Colour -> Rational -> Rational -> Int -> Int -> Int -> SomeDiagram
fusionExample c a b left right shared =
  let external = left + right
      nodes = external + shared
      links = [external .. nodes - 1]
      boxes =
        [ HG.Box (Spider c (phase a)) [] (reverse ([0 .. left - 1] ++ links))
        , HG.Box (Spider c (phase b)) [] ([left .. external - 1] ++ links)
        ]
  in HG.reifySorts (sorts external) \ @bs ->
       HG.SomeHypergraph (HG.unsafeOpenHypergraph @_ @'[] @bs (sorts nodes) [] [0 .. external - 1] boxes)

-- Decode graphs whose spiders all carry an output. Used to check the
-- resulting topology and phases independently of the port-rule templates.
boundaryGraph :: (a :: Diagram) ~> b -> Maybe ([Rational], [(Int, Int)])
boundaryGraph diagram = do
  unless (graphLike diagram) Nothing
  let (_, _, outs, boxes) = HG.hypergraphParts diagram
      vertices = [(i, p, ports box) | (i, box@(HG.Box (Spider Z p) _ _)) <- zip [0 :: Int ..] boxes]
      vertex n = case [(i, p) | (i, p, ps) <- vertices, n `elem` ps] of [v] -> Just v; _ -> Nothing
  boundary <- traverse vertex outs
  unless (length boundary == length vertices) Nothing
  let positions = Map.fromList (zip (map fst boundary) [0 ..])
      edge box = case ports box of
        [a, b] -> do
          (u, _) <- vertex a
          (v, _) <- vertex b
          i <- Map.lookup u positions
          j <- Map.lookup v positions
          pure (min i j, max i j)
        _ -> Nothing
  edges <- traverse edge [box | box@(HG.Box Hadamard _ _) <- boxes]
  pure (map snd boundary, nubOrd edges)

scalarFactors :: (a :: Diagram) ~> b -> (Int, Rational)
scalarFactors graph =
  let (_, _, _, boxes) = HG.hypergraphParts graph
  in (sum [power | HG.Box (Scalar power _) _ _ <- boxes], phase (sum [angle | HG.Box (Scalar _ angle) _ _ <- boxes]))

-- Boundary lists remain ordered even when their node references repeat.
someDiagram :: Int -> [Int] -> [Int] -> [HG.Box (Generator Rational) Int] -> SomeDiagram
someDiagram n ins outs boxes =
  HG.reifySorts (sorts (length ins)) \ @as ->
    HG.reifySorts (sorts (length outs)) \ @bs ->
      HG.SomeHypergraph (HG.unsafeOpenHypergraph @_ @as @bs (sorts n) ins outs boxes)

checkGraphLikeNormalisation :: (a :: Diagram) ~> b -> Property ()
checkGraphLikeNormalisation diagram = case normaliseGraphLike diagram of
  Left err -> testFailed err
  Right normal -> do
    check "graph-like invariant" (graphLike normal)
    let (_, ins, outs, _) = HG.hypergraphParts diagram
        (_, ins', outs', _) = HG.hypergraphParts normal
    expect "input count" (length ins) (length ins')
    expect "output count" (length outs) (length outs')
    case matrix diagram of
      Left err -> testFailed err
      Right original -> checkMatrix normal original
    case normaliseGraphLike normal of
      Left err -> testFailed err
      Right again -> check "normalisation is idempotent" (HG.isomorphic normal again)

graphLikeTests :: TestTree
graphLikeTests =
  testGroup
    "graph-like normalisation"
    [ testProperty "identity and swap preserve the boundary order" $ do
        let identity = obj @Q
            crossed = HG.unsafeOpenHypergraph @_ @'[ '(), '()] @'[ '(), '()] (sorts 2) [0, 1] [1, 0] []
        checkGraphLikeNormalisation identity
        checkGraphLikeNormalisation crossed
        case normaliseGraphLike identity of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (obj @1))
        case normaliseGraphLike crossed of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (swap @Nat @1 @1))
    , testProperty "cups and caps keep their repeated boundary references" $ do
        let cup = HG.unsafeOpenHypergraph @_ @'[] @'[ '(), '()] (sorts 1) [] [0, 0] []
            cap = HG.unsafeOpenHypergraph @_ @'[ '(), '()] @'[] (sorts 1) [0, 0] [] []
        checkGraphLikeNormalisation cup
        checkGraphLikeNormalisation cap
        case normaliseGraphLike cup of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (ZX.zSpider 0 :: ZX.ZX 0 2))
        case normaliseGraphLike cap of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (ZX.zSpider 0 :: ZX.ZX 2 0))
    , testProperty "a boundary Hadamard gets a distinct spider at each end" $ do
        checkGraphLikeNormalisation h
        case normaliseGraphLike h of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (ZX.hadamard @1))
    , testProperty "a multi-boundary phase spider is separated by identity paths" $ do
        let graph = spider @'[ '(), '()] @'[ '()] Z (1 / 4)
        checkGraphLikeNormalisation graph
        case normaliseGraphLike graph of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (ZX.zSpider (pi / 4) :: ZX.ZX 2 1))
    , testProperty "implicit fan-out, states and discards become explicit spiders" $ do
        let copy = HG.unsafeOpenHypergraph @_ @'[ '()] @'[ '(), '()] (sorts 1) [0] [0, 0] []
            state = HG.unsafeOpenHypergraph @_ @'[] @'[ '()] (sorts 1) [] [0] []
            discard = HG.unsafeOpenHypergraph @_ @'[ '()] @'[] (sorts 1) [0] [] []
        checkGraphLikeNormalisation copy
        checkGraphLikeNormalisation state
        checkGraphLikeNormalisation discard
        case normaliseGraphLike copy of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries ZX.zCopy)
    , testProperty "isolated wires and closed loops retain their scalar values" $ do
        let isolated = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] []
            loop = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 2) [] [] [HG.Box Hadamard [] [0, 1], HG.Box Hadamard [] [1, 0]]
        mapM_ checkGraphLikeNormalisation [isolated, loop]
        mapM_
          ( \graph -> case normaliseGraphLike graph of
              Left err -> testFailed err
              Right normal -> do
                checkMatrix normal (Map.singleton (0, 0) 2)
                let (ns, _, _, _) = HG.hypergraphParts normal
                expect "scalar wire materialised" 0 (length ns)
                expect "scalar two retained" (2, 0) (scalarFactors normal)
          )
          [isolated, loop]
    , testProperty "already graph-like diagrams keep their topology" $
        case openGraph 3 [0, 1 / 4, 0, 1 / 2] [(3, 0), (3, 1), (3, 2), (0, 1)] of
          HG.SomeHypergraph graph -> case normaliseGraphLike graph of
            Left err -> testFailed err
            Right normal -> check "existing normal form changed" (HG.isomorphic (materialiseJunctions graph) normal)
    , testProperty "generated diagrams preserve matrices, boundary order and normalisation idempotence" $ do
        n <- Falsify.gen (Gen.elem (1 :| [2, 3]))
        let node = Falsify.gen (Gen.elem (0 :| [1 .. n - 1]))
            boundary = do
              size <- Falsify.gen (Gen.elem (0 :| [1, 2]))
              replicateM size node
        ins <- boundary
        outs <- boundary
        count <- Falsify.gen (Gen.elem (0 :| [1, 2, 3]))
        boxes <- replicateM count do
          hadamard <- Falsify.gen (Gen.elem (False :| [True]))
          if hadamard
            then HG.Box Hadamard [] <$> replicateM 2 node
            else do
              c <- Falsify.gen (Gen.elem (Z :| [X]))
              p <- Falsify.gen (Gen.elem (0 :| [1 / 4, 1 / 2, 1, 3 / 2]))
              degree <- Falsify.gen (Gen.elem (0 :| [1, 2]))
              HG.Box (Spider c p) [] <$> replicateM degree node
        case someDiagram n ins outs boxes of { HG.SomeHypergraph graph -> checkGraphLikeNormalisation graph }
    , testProperty "local complementation restores a zero-phase boundary neighbour" $
        case openGraph 2 [1 / 2, 1 / 4, 1 / 2] [(2, 0), (2, 1)] of
          HG.SomeHypergraph graph -> case localComplementAt 2 graph of
            Left err -> testFailed err
            Right normal -> do
              expect "zero-phase boundary restored" (Just ([0, 7 / 4], [(0, 1)])) (boundaryGraph normal)
              checkGraphLikeNormalisation normal
              case matrix graph of
                Left err -> testFailed err
                Right original -> checkMatrix normal original
    , testProperty "invalid generator arities and unexpanded markers are rejected" $ do
        let bad label ps = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] [HG.Box label [] ps]
        check "unary H accepted" (isLeft (normaliseGraphLike (bad Hadamard [0])))
        check "wired scalar accepted" (isLeft (normaliseGraphLike (bad (Scalar 0 0) [0])))
        check "selection marker accepted" (isLeft (normaliseGraphLike (bad (Selected (1 / 2)) [0])))
        check "pivot marker accepted" (isLeft (normaliseGraphLike (bad (Pivot False 0) [0])))
    ]

-- A first complementation changes the other internal phase from 0 to -pi/2,
-- enabling a second step. Both output spiders remain attached throughout.
automaticExample :: SomeDiagram
automaticExample = openGraph 2 [1 / 4, 1 / 4, 1 / 2, 0] [(0, 2), (2, 3), (3, 1)]

checkAutomaticSimplification :: (a :: Diagram) ~> b -> Property ()
checkAutomaticSimplification diagram = case normaliseGraphLike diagram of
  Left err -> testFailed err
  Right _ -> case simplify diagram of
    Left err -> testFailed err
    Right (steps, result) -> do
      check "graph-like result" (graphLike result)
      expect "remaining local-complementation candidates" [] (localComplementCandidates result)
      expect "remaining pivot candidates" [] (pivotCandidates result)
      expect "remaining gadget pivots" [] (gadgetPivotCandidates result)
      check "remaining gadget reductions" (case gadgetReduction result of Nothing -> True; Just _ -> False)
      check "nonnegative step count" (steps >= 0)
      case matrix diagram of
        Left err -> testFailed err
        Right original -> checkMatrix result original
      case simplify result of
        Left err -> testFailed err
        Right (again, stable) -> do
          expect "normal form needs no further simplification" 0 again
          check "simplification is idempotent" (HG.isomorphic result stable)

automaticTests :: TestTree
automaticTests =
  testGroup
    "automatic Clifford simplification"
    [ testProperty "later steps find newly enabled internal spiders" $ case automaticExample of
        HG.SomeHypergraph graph -> do
          checkAutomaticSimplification graph
          case simplify graph of
            Left err -> testFailed err
            Right (steps, result) -> do
              expect "two local complementations" 2 steps
              expect "two internal spiders removed" 2 (spiderCount result)
              expect "resulting phases and edge" (Just ([1 / 4, 3 / 4], [(0, 1)])) (boundaryGraph result)
    , testProperty "the first eligible occurrence wins when several are available" $
        case openGraph 2 [1 / 4, 1 / 4, 1 / 2, 1 / 2] [(0, 2), (2, 3), (3, 1)] of
          HG.SomeHypergraph graph -> do
            expect "initial candidate order" [2, 3] (localComplementCandidates graph)
            checkAutomaticSimplification graph
            case simplifyInterior graph of
              Left err -> testFailed err
              Right (steps, result) -> do
                expect "first step makes the other phase zero" 1 steps
                let (_, _, outs, boxes) = HG.hypergraphParts result
                    phases = [p | wire <- outs, box@(HG.Box (Spider Z p) _ _) <- boxes, wire `elem` ports box]
                expect "first candidate selected" [7 / 4, 1 / 4] phases
    , testProperty "raw circuits are normalised before automatic selection" $ do
        let graph = x (1 / 2)
        checkAutomaticSimplification graph
        case simplify graph of
          Left err -> testFailed err
          Right (steps, result) -> do
            expect "one internal Clifford phase removed" 1 steps
            checkMatrix result (matrixEntries (ZX.xSpider (pi / 2) :: ZX.ZX 1 1))
    , testProperty "boundary padding is preserved without entering a cleanup cycle" $ do
        checkAutomaticSimplification (obj @Q)
        let copy = HG.unsafeOpenHypergraph @_ @'[ '()] @'[ '(), '()] (sorts 1) [0] [0, 0] []
        checkAutomaticSimplification copy
        case normaliseGraphLike copy of
          Left err -> testFailed err
          Right initial -> case simplify initial of
            Left err -> testFailed err
            Right (steps, result) -> do
              expect "zero-phase padding is not eligible" 0 steps
              check "padding was rebuilt" (HG.isomorphic initial result)
    , testProperty "isolated Clifford spiders retain their scalar and global phase" $
        mapM_
          ( \sign -> case openGraph 0 [phase (sign / 2)] [] of
              HG.SomeHypergraph graph -> do
                checkAutomaticSimplification graph
                case simplify graph of
                  Left err -> testFailed err
                  Right (steps, result) -> do
                    expect "one scalar expansion" 1 steps
                    expect "no spiders left" 0 (spiderCount result)
                    expect "exact scalar" (1, phase (sign / 4)) (scalarFactors result)
          )
          [1, -1]
    , testProperty "boundary Cliffords and isolated Pauli internal phases remain" $
        case openGraph 1 [1 / 2, 1 / 4, 0, 1] [(0, 1)] of
          HG.SomeHypergraph graph -> do
            checkAutomaticSimplification graph
            case simplify graph of
              Left err -> testFailed err
              Right (steps, result) -> do
                expect "no applicable rule" 0 steps
                expect "all four spiders remain" 4 (spiderCount result)
    , testProperty "each selected step removes one spider before searching again" $
        case openGraph 2 [0, 0, 0, 1 / 2, 3 / 2] [(0, 2), (1, 2), (2, 3), (3, 4), (4, 0)] of
          HG.SomeHypergraph graph -> checkSteps (spiderCount graph) graph
    , testProperty "generated graph-like diagrams reach a matrix-equivalent fixed point" $ do
        count <- Falsify.gen (Gen.elem (1 :| [2, 3, 4]))
        boundary <- Falsify.gen (Gen.elem (0 :| [1 .. min 2 count]))
        phases <- replicateM count (Falsify.gen (Gen.elem (0 :| [1 / 4, 1 / 2, 1, 3 / 2])))
        edges <-
          filterM (const (Falsify.gen (Gen.elem (False :| [True])))) [(i, j) | i <- [0 .. count - 1], j <- [i + 1 .. count - 1]]
        case openGraph boundary phases edges of { HG.SomeHypergraph graph -> checkAutomaticSimplification graph }
    ]
  where
    checkSteps :: Int -> (a :: Diagram) ~> b -> Property ()
    checkSteps remaining graph = case localComplementCandidates graph of
      [] -> check "final graph-like invariant" (graphLike graph)
      i : _ -> do
        check "step count exceeded initial spider count" (remaining > 0)
        case localComplementAt i graph of
          Left err -> testFailed err
          Right next -> do
            expect "one spider removed" (spiderCount graph - 1) (spiderCount next)
            check "graph-like invariant between steps" (graphLike next)
            checkSteps (remaining - 1) next

-- Two internal phases become gadgets on the same parity and cancel.
gadgetExample :: SomeDiagram
gadgetExample =
  openGraph
    2
    [1 / 3, 1 / 5, 0, 1 / 4, 0, 7 / 4]
    [(2, 3), (2, 0), (2, 1), (3, 0), (4, 5), (4, 0), (4, 1), (5, 0)]

-- Explicit gadgets with independently ordered supports, sharing target spiders.
gadgetGraph :: [Rational] -> [(Rational, Rational, [Int])] -> SomeDiagram
gadgetGraph targetPhases gadgets =
  let size = length targetPhases
      root k = size + 2 * k
      leaf k = root k + 1
  in openGraph
       size
       (targetPhases ++ concat [[a, b] | (a, b, _) <- gadgets])
       (concat [(root k, leaf k) : [(root k, t) | t <- targets] | (k, (_, _, targets)) <- zip [0 ..] gadgets])

checkGadgetReduction :: (a :: Diagram) ~> b -> Property ()
checkGadgetReduction graph = case gadgetReduction graph of
  Nothing -> testFailed "expected a gadget reduction"
  Just (Left err) -> testFailed err
  Just (Right result) -> do
    check "graph-like result" (graphLike result)
    check "termination measure decreased" (simplificationMeasure result < simplificationMeasure graph)
    case matrix graph of
      Left err -> testFailed err
      Right expected -> checkMatrix result expected

gadgetTests :: TestTree
gadgetTests =
  testGroup
    "phase gadgets"
    [ testProperty "gadget-pivot expansion preserves the exact tensor, including empty supports" $
        mapM_
          ( \(a, b, m, n, reverseH) ->
              HG.reifySorts (sorts (m + n)) \ @bs -> do
                let hs = if reverseH then [m + n + 1, m + n] else [m + n, m + n + 1]
                    graph =
                      HG.unsafeOpenHypergraph @_ @'[] @bs
                        (sorts (m + n + 2))
                        []
                        [0 .. m + n - 1]
                        [ HG.Box (Pivot False a) [] ([0 .. m - 1] ++ [m + n])
                        , HG.Box (Pivot True b) [] ((m + n + 1) : [m .. m + n - 1])
                        , HG.Box Hadamard [] hs
                        ]
                case gadgetPivotRules of
                  Left err -> testFailed err
                  Right compiled -> case R.rewritesCompiled compiled graph of
                    [(_, result)] -> case matrix graph of
                      Left err -> testFailed err
                      Right expected -> checkMatrix result expected
                    _ -> testFailed "expected one gadget expansion"
          )
          [ (a, b, m, n, reverseH)
          | a <- [0, 1]
          , b <- [1 / 4, -(1 / 3)]
          , m <- [0 .. 3]
          , n <- [0 .. 3]
          , m + n <= 4
          , reverseH <- [False, True]
          ]
    , matrixProperty "extraction preserves matrices with shared neighbours and existing edges" $ do
        a <- Falsify.gen (Gen.elem (0 :| [1]))
        b <- Falsify.gen (Gen.elem (1 / 4 :| [-(1 / 3), 5 / 7]))
        extra <-
          filterM
            (const (Falsify.gen (Gen.elem (False :| [True]))))
            [(3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (0, 1), (0, 2), (1, 2)]
        case openGraph 3 [1 / 4, 1 / 3, 1 / 7, a, b] ([(3, 4), (4, 2)] ++ extra) of
          HG.SomeHypergraph graph -> case gadgetPivotAt (3, 4) graph of
            Left err -> testFailed err
            Right result -> do
              check "graph-like extraction" (graphLike result)
              expect "extraction keeps the spider count" (spiderCount graph) (spiderCount result)
              check "extraction progress" (simplificationMeasure result < simplificationMeasure graph)
              case matrix graph of
                Left err -> testFailed err
                Right expected -> checkMatrix result expected
    , testProperty "equal target sets fuse regardless of port order, with exact scalar corrections" $
        mapM_
          ( \(size, phases) ->
              case gadgetGraph
                (replicate size 0)
                [(a, b, if even k then [0 .. size - 1] else reverse [0 .. size - 1]) | (k, (a, b)) <- zip [0 :: Int ..] phases] of
                HG.SomeHypergraph graph -> do
                  -- Run full matrix checks on two targets; larger supports check
                  -- topology, phases and the size-dependent scalar law.
                  when (size == 2) (checkGadgetReduction graph)
                  case gadgetReduction graph of
                    Just (Right result) -> do
                      check "graph-like result" (graphLike result)
                      check "termination measure decreased" (simplificationMeasure result < simplificationMeasure graph)
                      let view = zxGraph result
                          gadgets = phaseGadgets view
                          total = phase (sum [(1 - 2 * a) * b | (a, b) <- phases])
                      expect "one gadget remains" 1 (length gadgets)
                      expect "target set retained" [zBoundary view] [IS.fromList (gadgetTargets g) | g <- gadgets]
                      expect "combined phase" [total] [zPhases view Map.! gadgetLeaf g | g <- gadgets]
                      expect "normalised root" [0] [zPhases view Map.! gadgetRoot g | g <- gadgets]
                      expect "fusion scalar" ((1 - size) * (length phases - 1), phase (sum [a * b | (a, b) <- phases])) (scalarFactors result)
                    _ -> testFailed "expected fused gadget"
          )
          [ (size, phases)
          | size <- [2, 3, 4]
          , phases <- [[(0, 1 / 4), (0, 1 / 4), (0, 1 / 4)], [(1, 1 / 3), (0, 1 / 5)], [(1, 1 / 4), (1, 1 / 4), (0, 1 / 4)]]
          ]
    , testProperty "root pi phases negate the leaf phase and retain the global phase" $
        case gadgetGraph [1 / 3, 1 / 5] [(1, 1 / 4, [0, 1])] of
          HG.SomeHypergraph graph -> do
            checkGadgetReduction graph
            case gadgetReduction graph of
              Just (Right result) -> do
                let view = zxGraph result
                expect "negated phase" [7 / 4] [zPhases view Map.! gadgetLeaf g | g <- phaseGadgets view]
                expect "global phase" (0, 1 / 4) (scalarFactors result)
              _ -> testFailed "expected root normalisation"
    , testProperty "empty and singleton gadgets simplify without losing scalars or target phases" $
        mapM_
          ( \(size, a, b) -> case gadgetGraph (replicate size (1 / 3)) [(a, b, [0 .. size - 1])] of
              HG.SomeHypergraph graph -> do
                checkGadgetReduction graph
                case gadgetReduction graph of
                  Just (Right result) -> do
                    expect "gadget removed" size (spiderCount result)
                    expect "trivial gadget scalar" (if size == 0 then 1 else 0, phase (a * b)) (scalarFactors result)
                    when (size == 1) $ expect "phase absorbed" (Just ([phase (1 / 3 + (1 - 2 * a) * b)], [])) (boundaryGraph result)
                  _ -> testFailed "expected trivial gadget reduction"
          )
          [(size, a, b) | size <- [0, 1], a <- [0, 1], b <- [1 / 4, 1 / 3]]
    , testProperty "different supports are retained and existing gadgets are not extracted again" $
        case gadgetGraph [0, 0, 0] [(0, 1 / 4, [0, 1]), (0, 1 / 3, [1, 2])] of
          HG.SomeHypergraph graph -> do
            expect "no gadget pivot" [] (gadgetPivotCandidates graph)
            check "different supports merged" (case gadgetReduction graph of Nothing -> True; Just _ -> False)
            checkAutomaticSimplification graph
    , testProperty "fusion exposes Clifford reductions and cancelling gadgets disappear" $
        mapM_
          ( \phases -> case gadgetGraph [1 / 3, 1 / 5] [(0, p, [0, 1]) | p <- phases] of
              HG.SomeHypergraph graph -> do
                checkAutomaticSimplification graph
                case simplify graph of
                  Left err -> testFailed err
                  Right (_, result) -> do
                    expect "both gadgets eliminated" 2 (spiderCount result)
                    when (sum phases == 0) $ do
                      expect "unchanged boundary phases" (Just ([1 / 3, 1 / 5], [])) (boundaryGraph result)
                      expect "cancellation scalar" (-2, 0) (scalarFactors result)
          )
          [[1 / 4, -(1 / 4)], [1 / 4, 1 / 4]]
    , testProperty "the worked example extracts both phases before fusing and cancelling" $
        case gadgetExample of
          HG.SomeHypergraph graph -> do
            checkAutomaticSimplification graph
            case simplify graph of
              Left err -> testFailed err
              Right (steps, result) -> do
                expect "two extractions, one fusion and one pivot" 4 steps
                expect "only the boundary phases remain" (Just ([1 / 3, 1 / 5], [])) (boundaryGraph result)
                expect "exact scalar" (-4, 0) (scalarFactors result)
    , testProperty "fragment replacement preserves directed ports and isolated-wire scalars" $
        case gadgetGraph [1 / 3, 1 / 5] [(0, 1 / 4, [0, 1]), (0, 1 / 3, [1, 0])] of
          HG.SomeHypergraph graph -> do
            let (ns, ins, outs, boxes) = HG.hypergraphParts graph
                split (HG.Box l is os) = let (a, b) = splitAt 1 (reverse (is ++ os)) in HG.Box l a b
            case someDiagram (length ns + 1) ins outs (map split boxes) of
              HG.SomeHypergraph directed -> checkGadgetReduction directed
    , testProperty "generated diagrams reach an exact, idempotent gadget-aware fixed point" $ do
        size <- Falsify.gen (Gen.elem (1 :| [2, 3, 4, 5, 6]))
        boundary <- Falsify.gen (Gen.elem (0 :| [1 .. min 2 size]))
        phases <- replicateM size (Falsify.gen (Gen.elem (0 :| [1 / 4, 1 / 3, 1 / 2, 1, 3 / 2, 7 / 4])))
        edges <-
          filterM (const (Falsify.gen (Gen.elem (False :| [True])))) [(i, j) | i <- [0 .. size - 1], j <- [i + 1 .. size - 1]]
        case openGraph boundary phases edges of { HG.SomeHypergraph graph -> checkAutomaticSimplification graph }
    ]

-- An independent gate-list interpreter for small matrix checks. Bit zero in
-- the qubit list is the least significant matrix-index bit, as in ZX's tensor.
circuitMatrix :: Int -> [CircuitGate] -> Map.Map (Int, Int) (Complex Double)
circuitMatrix qubits gates =
  Map.fromList
    [ ((output, input), amplitude)
    | input <- [0 .. (1 `shiftL` qubits) - 1]
    , (output, amplitude) <- Map.toList (foldl' apply (Map.singleton input 1) gates)
    ]
  where
    apply state gate = Map.fromListWith (+) (concatMap (step gate) (Map.toList state))
    step (CNot c t) (basis, a) = [(if testBit basis c then basis `xor` (1 `shiftL` t) else basis, a)]
    step (ZPhase q p) (basis, a) = [(basis, if testBit basis q then a * mkPolar 1 (pi * fromRational p) else a)]
    step (Had q) (basis, a) =
      [ (basis, (if testBit basis q then negate a else a) / sqrt 2)
      , (basis `xor` (1 `shiftL` q), a / sqrt 2)
      ]

-- Exact tensor contraction grows rapidly with circuit width and graph density.
-- Keep broad random sampling for cheap graph checks, and bound these matrix checks.
matrixProperty :: String -> Property () -> TestTree
matrixProperty = testPropertyWith defaultTestOptions{overrideNumTests = Just 10}

checkReducedCircuit :: Int -> Int -> Int -> Property ()
checkReducedCircuit qubits depth seed =
  case cnotHadPhaseCircuit qubits depth seed of
    Left err -> testFailed err
    Right gates -> case circuitDiagram qubits gates of
      Left err -> testFailed err
      Right (HG.SomeHypergraph graph) -> case simplify graph >>= (\(_, normal) -> reduceEdges normal) of
        Left err -> testFailed err
        Right (_, result) -> do
          check "direct boundary attachments" (graphLike result)
          checkMatrix result (circuitMatrix qubits gates)
          case reduceEdges result of
            Left err -> testFailed err
            Right (again, stable) -> do
              expect "no further edge reductions" 0 again
              check "edge-reduction fixed point" (HG.isomorphic result stable)

pivotCongruenceTests :: TestTree
pivotCongruenceTests =
  testGroup
    "pivot congruence"
    [ testProperty "arbitrary phases and direct boundary attachments preserve exact matrices" $
        mapM_
          ( \(boundary, a, b) ->
              case openGraph boundary [1 / 3, 1 / 5, 1 / 7, a, b] [(3, 4), (3, 0), (3, 2), (4, 1), (4, 2), (0, 1), (1, 2)] of
                HG.SomeHypergraph graph -> case pivotCongruenceAt (3, 4) graph of
                  Left err -> testFailed err
                  Right result -> do
                    check "graph-like result" (graphLike result)
                    let DiagramSize oldSp oldH oldNc = diagramSize graph
                        DiagramSize newSp newH newNc = diagramSize result
                    expect "two phase spiders added" (oldSp + 2) newSp
                    expect "non-Clifford phases retained" oldNc newNc
                    expect "predicted cost change" (pivotCongruenceDelta (zxGraph graph) (3, 4)) (newSp + newH - oldSp - oldH)
                    case matrix graph of
                      Left err -> testFailed err
                      Right expected -> checkMatrix result expected
          )
          [(boundary, a, b) | boundary <- [0, 3, 4, 5], (a, b) <- [(0, 1 / 4), (1, 1 / 3), (1 / 4, 7 / 4), (1 / 2, 1 / 3)]]
    , testProperty "a dense joint neighbourhood becomes a smaller graph" $
        case openGraph
          7
          [1 / 4, 1 / 3, 0, 0, 0, 0, 0]
          ([(0, 1)] ++ [(0, i) | i <- [2 .. 4]] ++ [(1, i) | i <- [5, 6]] ++ [(i, j) | i <- [2 .. 4], j <- [5, 6]]) of
          HG.SomeHypergraph graph -> case pivotCongruenceAt (0, 1) graph of
            Left err -> testFailed err
            Right result -> do
              expect "predicted saving" (-2) (pivotCongruenceDelta (zxGraph graph) (0, 1))
              expect "two extra spiders, four fewer H edges" (DiagramSize 9 8 2) (diagramSize result)
    , matrixProperty "small generated circuits retain their independent unitary matrix" $ do
        qubits <- Falsify.gen (Gen.elem (2 :| [3]))
        depth <- Falsify.gen (Gen.elem (2 :| [5, 8]))
        seed <- Falsify.gen (Gen.elem (0 :| [1 .. 15]))
        checkReducedCircuit qubits depth seed
    , testProperty "three-qubit depth-eight seed 14 preserves its independent unitary matrix" $
        checkReducedCircuit 3 8 14
    , testProperty "invalid selections and non-graph-like inputs are rejected" $ do
        case openGraph 2 [1 / 4, 1 / 3, 0] [(0, 1), (1, 2)] of
          HG.SomeHypergraph graph ->
            mapM_
              (\pair -> check "invalid selection accepted" (isLeft (pivotCongruenceAt pair graph)))
              [(1, 0), (0, 2), (0, 0), (0, 999)]
        check "raw diagram accepted" (isLeft (pivotCongruenceAt (0, 1) before))
    , testProperty "a new Pauli pair may retain a cheaper representation than spider elimination" $
        case furtherExample of
          Left err -> testFailed err
          Right (steps, HG.SomeHypergraph result) -> case largeExample of
            Left err -> testFailed err
            Right (_, _, _, HG.SomeHypergraph initial) -> do
              let DiagramSize oldSp oldH oldNc = diagramSize initial
                  DiagramSize newSp newH newNc = diagramSize result
              check "a congruence improved the example" (steps > 0)
              check "strictly smaller graph" (newSp + newH < oldSp + oldH)
              check "fewer Hadamard edges" (newH < oldH)
              expect "non-Clifford phases retained" oldNc newNc
              check "direct boundary attachments" (graphLike result)
              case reduceEdges result of
                Left err -> testFailed err
                Right (again, stable) -> do
                  expect "idempotent edge search" 0 again
                  check "same graph" (HG.isomorphic (materialiseJunctions result) stable)
    ]

generatedCircuitTests :: TestTree
generatedCircuitTests =
  testGroup
    "generated circuits"
    [ testProperty "the seed reproduces a gate list of the requested length" $ do
        expect
          "extending depth preserves the prefix"
          (cnotHadPhaseCircuit 8 100 42)
          (fmap (take 100) (cnotHadPhaseCircuit 8 101 42))
        check "different seeds gave the same circuit" (cnotHadPhaseCircuit 8 100 42 /= cnotHadPhaseCircuit 8 100 43)
        case cnotHadPhaseCircuit 8 100 42 of
          Left err -> testFailed err
          Right gates -> do
            expect "gate count" 100 (length gates)
            check "generator produced invalid qubits" (case circuitDiagram 8 gates of Left _ -> False; Right _ -> True)
        check "single-qubit random CNOT generator accepted" (isLeft (cnotHadPhaseCircuit 1 100 42))
        check "negative depth accepted" (isLeft (cnotHadPhaseCircuit 8 (-1) 42))
        check "self CNOT accepted" (isLeft (circuitDiagram 2 [CNot 1 1]))
        check "out-of-range qubit accepted" (isLeft (circuitDiagram 2 [Had 2]))
    , testProperty "individual gates have unitary semantics in every qubit position" $
        mapM_
          ( \gate -> case circuitDiagram 3 [gate] of
              Left err -> testFailed err
              Right (HG.SomeHypergraph graph) -> checkMatrix graph (circuitMatrix 3 [gate])
          )
          ( [CNot c t | c <- [0 .. 2], t <- [0 .. 2], c /= t]
              ++ [Had q | q <- [0 .. 2]]
              ++ [ZPhase q p | q <- [0 .. 2], p <- [1 / 4, 1 / 2, -(1 / 3)]]
          )
    , testProperty "empty circuits preserve all identity wires, including the empty tensor" $
        mapM_
          ( \qubits -> case circuitDiagram qubits [] of
              Left err -> testFailed err
              Right (HG.SomeHypergraph graph) -> checkMatrix graph (circuitMatrix qubits [])
          )
          [0, 1, 3]
    , matrixProperty "small seeded circuits simplify to the independently interpreted matrix" $ do
        qubits <- Falsify.gen (Gen.elem (2 :| [3]))
        depth <- Falsify.gen (Gen.elem (0 :| [2, 5, 8]))
        seed <- Falsify.gen (Gen.elem (0 :| [1 .. 15]))
        case cnotHadPhaseCircuit qubits depth seed >>= circuitDiagram qubits of
          Left err -> testFailed err
          Right (HG.SomeHypergraph graph) -> case cnotHadPhaseCircuit qubits depth seed of
            Left err -> testFailed err
            Right gates -> do
              let expected = circuitMatrix qubits gates
              checkMatrix graph expected
              case simplify graph of
                Left err -> testFailed err
                Right (_, result) -> do
                  check "graph-like result" (graphLike result)
                  checkMatrix result expected
    , testProperty "the eight-qubit hundred-gate example reduces and retains its boundary" $
        case largeExample of
          Left err -> testFailed err
          Right (steps, HG.SomeHypergraph original, HG.SomeHypergraph normal, HG.SomeHypergraph result) -> do
            check "rewrites were applied" (steps > 0)
            check "graph-like input to strategy" (graphLike normal)
            check "graph-like result" (graphLike result)
            let bounds graph = let (_, ins, outs, _) = HG.hypergraphParts graph in (length ins, length outs)
                DiagramSize initialSpiders initialH initialPhases = diagramSize normal
                DiagramSize finalSpiders finalH finalPhases = diagramSize result
            expect "original circuit boundary" (8, 8) (bounds original)
            expect "simplified boundary" (8, 8) (bounds result)
            check "fewer spiders and Hadamards" (finalSpiders + finalH < initialSpiders + initialH)
            check "non-Clifford phases increased" (finalPhases <= initialPhases)
            case simplify result of
              Left err -> testFailed err
              Right (again, stable) -> do
                expect "no further reductions" 0 again
                check "fixed-point diagram" (HG.isomorphic (materialiseJunctions result) stable)
    , testProperty "scalar collection cancels exact factors and preserves isolated-wire scalars" $ do
        let graph =
              HG.unsafeOpenHypergraph @_ @'[] @'[]
                (sorts 1)
                []
                []
                [HG.Box (Scalar 1 (1 / 2)) [] [], HG.Box (Scalar (-1) (3 / 2)) [] []]
            compact = collectScalars graph
        expect "scalar factors cancel" (0, 0) (scalarFactors compact)
        expect "no identity scalar boxes" 0 (boxCount compact)
        checkMatrix compact (Map.singleton (0, 0) 2)
        checkGraphLikeNormalisation graph
    ]

boundaryExample :: SomeDiagram
boundaryExample = openGraph 3 [1 / 2, 1 / 3, 1 / 5, 0] [(3, 0), (3, 1), (3, 2), (0, 1)]

boundaryPivotTests :: TestTree
boundaryPivotTests =
  testGroup
    "boundary pivoting"
    [ testProperty "Pauli, Clifford and non-Clifford boundary phases preserve exact matrices" $
        mapM_
          ( \(a, b) -> case openGraph 3 [b, 1 / 3, 1 / 5, a] [(3, 0), (3, 1), (3, 2), (0, 1), (1, 2)] of
              HG.SomeHypergraph graph -> case boundaryPivotAt (3, 0) graph of
                Left err -> testFailed err
                Right result -> do
                  check "direct and distinct Z boundary attachments" (graphLike result)
                  case matrix graph of
                    Left err -> testFailed err
                    Right expected -> checkMatrix result expected
          )
          [(a, b) | a <- [0, 1], b <- [0, 1, 1 / 2, 3 / 2, 1 / 4, 1 / 3]]
    , matrixProperty "generated overlaps, port directions and mixed boundaries preserve matrices" $ do
        a <- Falsify.gen (Gen.elem (0 :| [1]))
        b <- Falsify.gen (Gen.elem (0 :| [1, 1 / 2, 1 / 4, 1 / 3]))
        extra <- filterM (const (Falsify.gen (Gen.elem (False :| [True])))) [(3, 1), (3, 2), (0, 2), (1, 2)]
        case openGraph 3 [b, 1 / 3, 1 / 5, a] ([(3, 0), (0, 1)] ++ extra) of
          HG.SomeHypergraph graph -> do
            let (ns, _, outs, boxes) = HG.hypergraphParts graph
                split (HG.Box l is os) = let (ps, qs) = splitAt 1 (reverse (is ++ os)) in HG.Box l ps qs
            case someDiagram (length ns + 1) (reverse (take 2 outs)) (drop 2 outs) (map split boxes) of
              HG.SomeHypergraph directed -> do
                case boundaryPivotAt (3, 0) directed of
                  Left err -> testFailed err
                  Right result -> do
                    check "graph-like result" (graphLike result)
                    case matrix directed of
                      Left err -> testFailed err
                      Right expected -> checkMatrix result expected
                checkAutomaticSimplification directed
    , testProperty "a boundary round removes interior structure even when padding adds spiders" $
        case openGraph 3 [1 / 4, 1 / 3, 1 / 5, 0] [(3, 0), (3, 1), (3, 2), (0, 1)] of
          HG.SomeHypergraph graph -> do
            expect "one interior spider" 1 (interiorSize graph)
            case boundaryPivotAt (3, 0) graph of
              Left err -> testFailed err
              Right padded -> do
                check "gadget and padding add spiders" (spiderCount padded > spiderCount graph)
            case boundaryReduction graph of
              Left err -> testFailed err
              Right Nothing -> testFailed "expected an improving boundary round"
              Right (Just (steps, result)) -> do
                check "positive step count" (steps > 0)
                expect "no interior structure outside gadgets" 0 (interiorSize result)
                check "boundary convention" (graphLike result)
            checkAutomaticSimplification graph
    , testProperty "pivots through existing zero-phase boundary padding without counting it as interior" $
        mapM_
          ( \p -> case openGraph 3 [0, 1 / 3, 1 / 5, p, 0] [(0, 3), (4, 3), (4, 1), (4, 2), (3, 1)] of
              HG.SomeHypergraph graph -> do
                expect "boundary position behind padding" (Just [0]) (Map.lookup 3 (boundaryAttachments graph))
                check "padded endpoint is not an interior candidate" (all ((/= 3) . fst) (boundaryPivotCandidates graph))
                case boundaryPivotAt (4, 3) graph of
                  Left err -> testFailed err
                  Right result -> do
                    check "direct Z attachments" (graphLike result)
                    case matrix graph of
                      Left err -> testFailed err
                      Right expected -> checkMatrix result expected
                checkAutomaticSimplification graph
          )
          [1 / 4, 1]
    , testProperty "identity, Hadamard, phase and copy padding do not cause reverse-pivot cycles" $ do
        let copy = HG.unsafeOpenHypergraph @_ @'[ '()] @'[ '(), '()] (sorts 1) [0] [0, 0] []
        checkAutomaticSimplification copy
        mapM_ checkAutomaticSimplification [obj @Q, h, z (1 / 4)]
        mapM_
          ( \graph -> case normaliseGraphLike graph of
              Left err -> testFailed err
              Right normal -> do
                expect "no padding-only boundary pivot" [] (boundaryPivotCandidates normal)
                case simplify normal of
                  Left err -> testFailed err
                  Right (steps, result) -> do
                    expect "padding needs no rewrite" 0 steps
                    check "padding was changed" (HG.isomorphic normal result)
          )
          [obj @Q, h, z (1 / 4)]
    , testProperty "selection rejects boundaries as interior endpoints, gadgets and missing edges" $ do
        case openGraph 2 [1 / 4, 1 / 3, 0, 1 / 4] [(2, 0), (2, 1), (3, 1)] of
          HG.SomeHypergraph graph -> do
            expect "boundary candidates" [(2, 0), (2, 1)] (boundaryPivotCandidates graph)
            mapM_
              (\pair -> check "invalid boundary pivot accepted" (isLeft (boundaryPivotAt pair graph)))
              [(0, 2), (3, 1), (2, 999), (2, 3)]
        case gadgetGraph [1 / 3, 1 / 5] [(0, 1 / 4, [0, 1])] of
          HG.SomeHypergraph graph -> expect "existing gadget root is protected" [] (boundaryPivotCandidates graph)
    , testProperty "the worked boundary Clifford needs one pivot and two local complementations" $
        case boundaryExample of
          HG.SomeHypergraph graph -> do
            checkAutomaticSimplification graph
            case simplify graph of
              Left err -> testFailed err
              Right (steps, result) -> do
                expect "one boundary round" 3 steps
                expect "no interior structure outside the boundary frame" 0 (interiorSize result)
                check "direct Z attachments" (graphLike result)
    , testProperty "automatic boundary rounds leave no further improving pivot" $
        case openGraph 3 [1 / 2, 1 / 3, 1 / 5, 0, 1] [(3, 0), (3, 1), (3, 4), (4, 2)] of
          HG.SomeHypergraph graph -> do
            checkAutomaticSimplification graph
            case simplify graph of
              Left err -> testFailed err
              Right (_, result) -> case boundaryReduction result of
                Left err -> testFailed err
                Right next -> check "an improving boundary round remains" (case next of Nothing -> True; Just _ -> False)
    ]

pivotTests :: TestTree
pivotTests =
  testGroup
    "internal Pauli pivoting"
    [ testProperty "the expansion is an exact tensor identity, including empty sides" $
        mapM_
          ( \(a, b, m, n, reverseH) ->
              HG.reifySorts (sorts (m + n)) \ @bs -> do
                let hs = if reverseH then [m + n + 1, m + n] else [m + n, m + n + 1]
                    graph =
                      HG.unsafeOpenHypergraph @_ @'[] @bs
                        (sorts (m + n + 2))
                        []
                        [0 .. m + n - 1]
                        [ HG.Box (Pivot False a) [] ([0 .. m - 1] ++ [m + n])
                        , HG.Box (Pivot True b) [] ((m + n + 1) : [m .. m + n - 1])
                        , HG.Box Hadamard [] hs
                        ]
                case pivotRules of
                  Left err -> testFailed err
                  Right compiled -> case R.rewritesCompiled compiled graph of
                    [(_, expanded)] -> case matrix graph of
                      Left err -> testFailed err
                      Right expected -> checkMatrix expanded expected
                    _ -> testFailed "expected one selected pivot expansion"
          )
          [(a, b, m, n, reverseH) | a <- [0, 1], b <- [0, 1], m <- [0 .. 3], n <- [0 .. 3], m + n <= 4, reverseH <- [False, True]]
    , testProperty "shared neighbours and existing edges have the correct phases and scalar" $
        mapM_
          ( \(a, b, existing) ->
              case openGraph 3 [1 / 4, 1 / 3, 1 / 7, a, b] ([(3, 4), (3, 0), (4, 1), (3, 2), (4, 2)] ++ existing) of
                HG.SomeHypergraph graph -> case pivotAt (3, 4) graph of
                  Left err -> testFailed err
                  Right result -> do
                    check "graph-like result" (graphLike result)
                    expect "both endpoints removed" 3 (spiderCount result)
                    expect
                      "complemented edges and shifted phases"
                      (Just (map phase [1 / 4 + b, 1 / 3 + a, 1 / 7 + a + b + 1], filter (`notElem` existing) [(0, 1), (0, 2), (1, 2)]))
                      (boundaryGraph result)
                    expect "exact scalar correction" (negate (2 * length existing), phase (a * b)) (scalarFactors result)
                    case matrix graph of
                      Left err -> testFailed err
                      Right expected -> checkMatrix result expected
          )
          [(a, b, existing) | a <- [0, 1], b <- [0, 1], existing <- subsequences [(0, 1), (0, 2), (1, 2)]]
    , testProperty "generated neighbourhood overlaps preserve exact matrices" $ do
        count <- Falsify.gen (Gen.elem (0 :| [1, 2, 3]))
        a <- Falsify.gen (Gen.elem (0 :| [1]))
        b <- Falsify.gen (Gen.elem (0 :| [1]))
        phases <- replicateM count (Falsify.gen (Gen.elem (0 :| [1 / 4, 1 / 2, 1, 3 / 2])))
        let possible = [(i, j) | i <- [0 .. count + 1], j <- [i + 1 .. count + 1], (i, j) /= (count, count + 1)]
        extra <- filterM (const (Falsify.gen (Gen.elem (False :| [True])))) possible
        case openGraph count (phases ++ [a, b]) ((count, count + 1) : extra) of
          HG.SomeHypergraph graph -> case pivotAt (count, count + 1) graph of
            Left err -> testFailed err
            Right result -> do
              check "graph-like result" (graphLike result)
              expect "two spiders removed" count (spiderCount result)
              case matrix graph of
                Left err -> testFailed err
                Right expected -> checkMatrix result expected
    , testProperty "selection excludes boundary, non-Pauli, non-adjacent and missing spiders" $
        case openGraph 1 [0, 0, 1, 1 / 4, 0] [(0, 1), (1, 2), (2, 3)] of
          HG.SomeHypergraph graph -> do
            expect "eligible pair" [(1, 2)] (pivotCandidates graph)
            mapM_
              (\pair -> check "invalid pair accepted" (isLeft (pivotAt pair graph)))
              [(0, 1), (2, 3), (1, 4), (2, 1), (1, 999), (1, 1)]
    , testProperty "local complementation enables a subsequent pivot" $
        case openGraph 1 [1 / 4, 1 / 2, 1 / 2, 1 / 2] [(1, 2), (1, 3), (0, 2)] of
          HG.SomeHypergraph graph -> do
            -- The first LC turns its two half-phase neighbours into a Pauli pair.
            checkAutomaticSimplification graph
            case simplify graph of
              Left err -> testFailed err
              Right (steps, result) -> do
                expect "two elimination steps" 2 steps
                expect "all internal spiders removed" 1 (spiderCount result)
    ]

localComplementTests :: TestTree
localComplementTests =
  testGroup
    "local complementation"
    [ testProperty "the expansion is an exact tensor identity at degrees zero through four" $
        mapM_
          ( \(sign, degree) ->
              HG.reifySorts (sorts degree) \ @bs -> do
                let graph =
                      HG.unsafeOpenHypergraph @_ @'[] @bs
                        (sorts degree)
                        []
                        [0 .. degree - 1]
                        [HG.Box (Selected (phase (sign / 2))) [] [0 .. degree - 1]]
                case localComplementRules of
                  Left err -> testFailed err
                  Right compiled -> case R.rewritesCompiled compiled graph of
                    [(_, expanded)] -> case matrix graph of
                      Left err -> testFailed err
                      Right expected -> do
                        checkMatrix expanded expected
                        case optimise expanded of
                          Left err -> testFailed err
                          Right (_, cleaned) -> checkMatrix cleaned expected
                    _ -> testFailed "expected one selected expansion"
          )
          [(sign, degree) | sign <- [1, -1], degree <- [0 .. 4]]
    , testProperty "one selected step toggles neighbour edges, shifts phases and preserves scalars" $
        mapM_
          ( \(sign, existing) ->
              case openGraph 3 [1 / 4, 1 / 3, 1 / 7, phase (sign / 2)] ([(3, i) | i <- [0 .. 2]] ++ existing) of
                HG.SomeHypergraph graph -> do
                  check "input graph-like" (graphLike graph)
                  case localComplementAt 3 graph of
                    Left err -> testFailed err
                    Right after -> do
                      let allPairs = [(0, 1), (0, 2), (1, 2)]
                          expected = (map (phase . subtract (sign / 2)) [1 / 4, 1 / 3, 1 / 7], filter (`notElem` existing) allPairs)
                      expect "complemented boundary graph" (Just expected) (boundaryGraph after)
                      expect "exact scalar correction" (1 - 2 * length existing, phase (sign / 4)) (scalarFactors after)
                      case matrix graph of
                        Left err -> testFailed err
                        Right original -> checkMatrix after original
          )
          [(sign, edges) | sign <- [1, -1], edges <- [[], [(0, 1)], [(0, 1), (1, 2)], [(0, 1), (0, 2), (1, 2)]]]
    , testProperty "Hadamard loop cleanup adds pi and retains inverse sqrt two" $
        mapM_
          ( \p -> case openGraph 1 [p] [(0, 0)] of
              HG.SomeHypergraph graph -> do
                checkOptimisation graph
                case optimise graph of
                  Left err -> testFailed err
                  Right (_, after) -> do
                    expect "phase correction" (Just ([phase (p + 1)], [])) (boundaryGraph after)
                    expect "scalar correction" (-1, 0) (scalarFactors after)
          )
          [0, 1 / 4, 1, 5 / 7]
    , testProperty "parallel Hadamards cancel with factor one half for either port ordering" $
        mapM_
          ( \reverseSecond -> case openGraph 2 [1 / 4, 1 / 3] [(0, 1), if reverseSecond then (1, 0) else (0, 1)] of
              HG.SomeHypergraph graph -> do
                checkOptimisation graph
                case optimise graph of
                  Left err -> testFailed err
                  Right (_, after) -> do
                    expect "parallel edges removed" (Just ([1 / 4, 1 / 3], [])) (boundaryGraph after)
                    expect "scalar correction" (-2, 0) (scalarFactors after)
          )
          [False, True]
    , testProperty "selection rejects boundaries, non-Clifford phases and non-simple graphs" $ do
        case openGraph 1 [1 / 2, 1 / 4] [(0, 1)] of
          HG.SomeHypergraph graph -> do
            check "boundary selected" (isLeft (localComplementAt 0 graph))
            check "non-Clifford selected" (isLeft (localComplementAt 1 graph))
            check "missing vertex selected" (isLeft (localComplementAt 999 graph))
        case openGraph 1 [1 / 4, 1 / 2] [(0, 1), (0, 1)] of
          HG.SomeHypergraph graph -> check "parallel input accepted" (isLeft (localComplementAt 1 graph))
    ]

matrixEntries :: ZX.ZX i o -> Map.Map (Int, Int) (Complex Double)
matrixEntries (ZX.ZX m) = Map.mapKeys (bimap fromEnum fromEnum) m

sameMatrix :: Map.Map (Int, Int) (Complex Double) -> Map.Map (Int, Int) (Complex Double) -> Bool
sameMatrix a b = all ZX.isZero (Map.elems (Map.unionWith (+) a (Map.map negate b)))

checkMatrix :: (a :: Diagram) ~> b -> Map.Map (Int, Int) (Complex Double) -> Property ()
checkMatrix graph expected = case matrix graph of
  Left err -> testFailed err
  Right actual -> check "matrix matches existing ZX semantics" (sameMatrix expected actual)

checkOptimisation :: (a :: Diagram) ~> b -> Property ()
checkOptimisation graph = case optimise graph of
  Left err -> testFailed err
  Right (steps, after) -> do
    check "rewrites applied" (steps > 0)
    case matrix graph of
      Left err -> testFailed err
      Right original -> checkMatrix after original
    case optimise after of
      Left err -> testFailed err
      Right (n, stable) -> do
        expect "fixed point" 0 n
        check "stable graph" (HG.isomorphic after stable)

beforeMatrix :: ZX.ZX 2 2
beforeMatrix =
  (ZX.zSpider @1 @1 (pi / 4) ** ZX.hadamard @1)
    . (ZX.zSpider @1 @1 (-(pi / 4)) ** ZX.hadamard @1)
    . ZX.cnot
    . ((ZX.hadamard @1 . ZX.xSpider (pi / 4) . ZX.hadamard @1) ** obj @1)

test :: TestTree
test =
  testGroup
    "ZX rewriting"
    [ pivotCongruenceTests
    , generatedCircuitTests
    , boundaryPivotTests
    , gadgetTests
    , pivotTests
    , automaticTests
    , graphLikeTests
    , localComplementTests
    , testProperty "the worked circuit simplifies and preserves its matrix including scalars" $ do
        checkMatrix before (matrixEntries beforeMatrix)
        checkOptimisation before
        checkGraphLikeNormalisation before
        case optimise before of
          Left err -> testFailed err
          Right (_, after) -> check "fewer generators" (boxCount after < boxCount before)
    , testProperty "exact rational phases fuse modulo two, including newly created phases" $ do
        let graph = z (1 / 3) . z (1 / 5) . z (22 / 15)
        checkOptimisation graph
        case optimise graph of
          Left err -> testFailed err
          Right (_, after) -> do
            expect "all three phases cancel" 0 (boxCount after)
            checkMatrix after (matrixEntries (obj @1))
    , matrixProperty "fusion supports arbitrary degrees, port orders, phases and multiple connecting wires" $ do
        c <- Falsify.gen (Gen.elem (Z :| [X]))
        a <- Falsify.gen (Gen.elem (0 :| [1 / 4, -(1 / 3), 5 / 7]))
        b <- Falsify.gen (Gen.elem (0 :| [-(1 / 4), 2 / 3, 11 / 7]))
        left <- Falsify.gen (Gen.elem (0 :| [1, 2, 3]))
        right <- Falsify.gen (Gen.elem (0 :| [1, 2, 3]))
        shared <- Falsify.gen (Gen.elem (1 :| [2, 3]))
        case fusionExample c a b left right shared of { HG.SomeHypergraph graph -> checkOptimisation graph }
    , testProperty "compiled captures handle degrees created by earlier fusions" $ do
        let graph =
              HG.unsafeOpenHypergraph @_ @'[] @'[ '(), '(), '(), '(), '()]
                (sorts 7)
                []
                [2, 3, 4, 5, 6]
                [HG.Box (Spider Z (1 / 3)) [] [0, 3, 4], HG.Box (Spider Z (1 / 5)) [] [0, 1, 5], HG.Box (Spider Z (1 / 7)) [] [1, 2, 6]]
        checkOptimisation graph
        case optimise graph of
          Left err -> testFailed err
          Right (_, after) -> do
            expect "one degree-five spider" 1 (boxCount after)
            checkMatrix after (matrixEntries (ZX.zSpider (pi * (1 / 3 + 1 / 5 + 1 / 7)) :: ZX.ZX 0 5))
    , testProperty "colour change and Hadamard cancellation implement H-X-H = Z" $ do
        p <- Falsify.gen (Gen.elem (0 :| [1 / 4, -(1 / 3), 5 / 7]))
        let graph = h . x p . h
        checkMatrix graph (matrixEntries (ZX.zSpider (pi * fromRational p) :: ZX.ZX 1 1))
        checkOptimisation graph
        case optimise graph of
          Left err -> testFailed err
          Right (_, after) -> do
            let (_, _, _, boxes) = HG.hypergraphParts after
            expect "only a Z phase remains" [Spider Z (phase p) | phase p /= 0] (map HG.label boxes)
    , testProperty "independent rules are applied in the same compiled batch" $ do
        let graph = (z (1 / 3) . z (1 / 5)) ** (h . h)
            (ns, is, os, boxes) = HG.hypergraphParts graph
            states = map stateBox boxes
        case rules of
          Left err -> testFailed err
          Right compiled -> do
            let (n, after) = R.rewriteBatchCompiled compiled (HG.unsafeOpenHypergraph @_ @'[ '(), '()] @'[ '(), '()] ns is os states)
            expect "two disjoint rewrites" 2 n
            expect "one phase remains" 1 (boxCount after)
            checkMatrix after (matrixEntries ((ZX.zSpider (pi * (1 / 3 + 1 / 5)) :: ZX.ZX 1 1) ** obj @1))
    , testProperty "closed double-H and identity-spider loops retain their scalar two" $ do
        let loop boxes = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 2) [] [] boxes
            doubleH = loop [HG.Box Hadamard [] [0, 1], HG.Box Hadamard [] [1, 0]]
            identityLoop = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] [HG.Box (Spider X 0) [] [0, 0]]
        mapM_ (\g -> checkOptimisation g >> checkMatrix g (Map.singleton (0, 0) 2)) [doubleH, identityLoop]
    , testProperty "colour change preserves a nonzero phase on a self-loop" $ do
        let graph = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] [HG.Box (Spider X (1 / 3)) [] [0, 0]]
        checkOptimisation graph
        checkMatrix graph (matrixEntries (ZX.zSpider (pi / 3) :: ZX.ZX 0 0))
    , testProperty "a closed zero scalar remains zero" $ do
        let graph = HG.unsafeOpenHypergraph @_ @'[] @'[] [] [] [] [HG.Box (Spider X 1) [] []]
        checkOptimisation graph
        checkMatrix graph Map.empty
    , testProperty "cups, repeated boundaries and isolated scalar wires survive interpretation" $ do
        let cup = HG.unsafeOpenHypergraph @_ @'[] @'[ '(), '()] (sorts 1) [] [0, 0] []
            scalar = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] []
        checkMatrix cup (matrixEntries (ZX.zSpider 0 :: ZX.ZX 0 2))
        checkMatrix scalar (Map.singleton (0, 0) 2)
    ]
