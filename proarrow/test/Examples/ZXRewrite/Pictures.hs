-- | Worked ZX examples and their Graphviz output.
module Examples.ZXRewrite.Pictures where

import Data.Containers.ListUtils (nubOrd)
import Data.Map.Strict qualified as Map
import Data.Ratio (denominator, numerator)
import Prelude hiding (id, (**), (.))

import Examples.ZXRewrite.Diagram
import Examples.ZXRewrite.Simplify
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), (//))

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

furtherExample :: Either String (Int, SomeDiagram)
furtherExample = do
  (_, _, _, HG.SomeHypergraph graph) <- largeExample
  (steps, result) <- reduceEdges graph
  result // pure (steps, HG.SomeHypergraph result)

-- A first complementation changes the other internal phase from 0 to -pi/2,
-- enabling a second step. Both output spiders remain attached throughout.
automaticExample :: SomeDiagram
automaticExample = openGraph 2 [1 / 4, 1 / 4, 1 / 2, 0] [(0, 2), (2, 3), (3, 1)]

-- Two internal phases become gadgets on the same parity and cancel.
gadgetExample :: SomeDiagram
gadgetExample =
  openGraph
    2
    [1 / 3, 1 / 5, 0, 1 / 4, 0, 7 / 4]
    [(2, 3), (2, 0), (2, 1), (3, 0), (4, 5), (4, 0), (4, 1), (5, 0)]

boundaryExample :: SomeDiagram
boundaryExample = openGraph 3 [1 / 2, 1 / 3, 1 / 5, 0] [(3, 0), (3, 1), (3, 2), (0, 1)]

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
                ++ quoted (scalarLabel power angle)
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
            Scalar power angle -> (scalarLabel power angle, "#e5e7eb", "box")
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
scalarLabel :: Int -> Rational -> String
scalarLabel power angle = "√2^" ++ show power ++ if angle == 0 then "" else " exp(" ++ phaseLabel angle ++ " i)"

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
