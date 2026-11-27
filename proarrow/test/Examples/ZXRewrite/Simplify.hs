-- | ZX cleanup rules, graph-like normalisation and simplification strategies.
module Examples.ZXRewrite.Simplify where

import Control.Monad (unless)
import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List (mapAccumL)
import Data.Map.Strict qualified as Map
import Prelude hiding ((.))

import Examples.ZXRewrite.Diagram
import Examples.ZXRewrite.Rules
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Core (CategoryOf (..), Promonad (..), (//))
import Proarrow.Tools.HypergraphRewrite qualified as R

-- Fixed labels and captured port lists form one rule set, compiled once.
-- Captured sequences retain their order; the surrounding captures let a
-- connecting wire occur at any port position on a symmetric spider.
rules :: Either String (R.CompiledRules Int () (Generator Rational))
rules = cleanupRules True

-- Preserve boundary identity paths during elimination cleanup.
structuralCleanup :: Either String (R.CompiledRules Int () (Generator Rational))
structuralCleanup = cleanupRules False

cleanupRules :: Bool -> Either String (R.CompiledRules Int () (Generator Rational))
cleanupRules removeIdentities = do
  learned <- learnedHadamardRules
  fixed <- fixedCleanupRules removeIdentities 0 (\a b -> phase (a + b)) learned
  colour <- colourChangeRule
  R.compileRules (zip [0 :: Int ..] (map snd fixed ++ [colour]))

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

-- Nullary scalar multiplication leaves the diagram wiring intact.
collectScalars
  :: (a :: Diagram) ~> b -> HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram)
collectScalars diagram =
  diagram //
    let (ns, ins, outs, boxes) = HG.hypergraphParts diagram
    in HG.unsafeOpenHypergraph ns ins outs (collectScalarBoxes 0 1 boxes)

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
        owners =
          IM.fromListWith
            min
            [(wire, i) | (i, box@(HG.Box (Spider Z _) _ _)) <- zip [0 ..] boxes, wire <- ports box]
        repair (next, claimed, padded, paths) wire =
          case IM.lookup wire owners of
            Just i | IS.notMember i claimed -> ((next, IS.insert i claimed, padded, paths), wire)
            Nothing
              | IS.notMember wire padded ->
                  ((next + 1, claimed, IS.insert wire padded, [HG.Box (Spider Z 0) [] [next, wire]] : paths), next)
            _ ->
              let path =
                    [ HG.Box (Spider Z 0) [] [next, next + 1]
                    , HG.Box Hadamard [] [next + 1, next + 2]
                    , HG.Box (Spider Z 0) [] [next + 2, next + 3]
                    , HG.Box Hadamard [] [next + 3, wire]
                    ]
              in ((next + 4, claimed, padded, path : paths), next)
        ((end, _, _, additions), boundary) = mapAccumL repair (length ns, IS.empty, IS.empty, []) (ins ++ outs)
        (inputs, outputs) = splitAt (length ins) boundary
    in HG.unsafeOpenHypergraph (ns ++ sorts (end - length ns)) inputs outputs (boxes ++ concat (reverse additions))

restoreGraphLike
  :: String
  -> (a :: Diagram) ~> b
  -> Either String (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
restoreGraphLike failure diagram = do
  let result = collectScalars (repairBoundaries (materialiseJunctions diagram))
  unless (graphLike result) (Left failure)
  pure result

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
    else optimise explicit >>= restoreGraphLike "normaliseGraphLike: graph-like invariants were not established" . snd

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
    originalSize = interiorSize current
    try [] = pure Nothing
    try (pair : rest) = do
      pivoted <- boundaryPivotAt pair current
      (steps, next) <- simplifyInterior pivoted
      if interiorSize next < originalSize
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
    restoreGraphLike (name ++ ": cleanup did not restore graph-like form") cleaned
  _ -> Left (name ++ ": expansion did not select exactly one match")
