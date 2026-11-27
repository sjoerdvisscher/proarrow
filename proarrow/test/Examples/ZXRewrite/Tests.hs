-- | ZX simplification and independent matrix regressions.
module Examples.ZXRewrite.Tests (test) where

import Control.Monad (filterM, replicateM, unless, void, when)
import Data.Bits (shiftL, testBit, xor)
import Data.Complex (Complex, mkPolar)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (isLeft)
import Data.IntSet qualified as IS
import Data.List (sort, subsequences)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as Map
import GHC.TypeNats (Nat)
import Test.Falsify (Property, testFailed)
import Test.Falsify qualified as Falsify
import Test.Falsify.Generator qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (TestOptions (..), testProperty, testPropertyWith)
import Prelude hiding (id, (**), (.))

import Examples.ZXRewrite.Diagram
import Examples.ZXRewrite.Overlaps (overlapTests)
import Examples.ZXRewrite.Pictures
  ( automaticExample
  , before
  , boundaryExample
  , furtherExample
  , gadgetExample
  , largeExample
  )
import Examples.ZXRewrite.Simplify
import Proarrow.Category.Instance.OpenHypergraph (W1, W2, W5)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.ZX qualified as ZX
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Testing (check, expect)
import Proarrow.Testing.Laws (defaultTestOptions)
import Proarrow.Tools.HypergraphRewrite qualified as R

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

checkGraphLikeNormalisation :: (a :: Diagram) ~> b -> Property ()
checkGraphLikeNormalisation diagram = do
  normal <- either testFailed pure (normaliseGraphLike diagram)
  check "graph-like invariant" (graphLike normal)
  let (_, ins, outs, _) = HG.hypergraphParts diagram
      (_, ins', outs', _) = HG.hypergraphParts normal
  expect "input count" (length ins) (length ins')
  expect "output count" (length outs) (length outs')
  either testFailed (checkMatrix normal) (matrix diagram)
  again <- either testFailed pure (normaliseGraphLike normal)
  check "normalisation is idempotent" (HG.isomorphic normal again)

graphLikeTests :: TestTree
graphLikeTests =
  testGroup
    "graph-like normalisation"
    [ testProperty "identity and swap preserve the boundary order" $ do
        let identity = obj @Q
            crossed = HG.unsafeOpenHypergraph @_ @W2 @W2 (sorts 2) [0, 1] [1, 0] []
        checkGraphLikeNormalisation identity
        checkGraphLikeNormalisation crossed
        case normaliseGraphLike identity of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (obj @1))
        case normaliseGraphLike crossed of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (swap @Nat @1 @1))
    , testProperty "cups and caps keep their repeated boundary references" $ do
        let cup = HG.unsafeOpenHypergraph @_ @'[] @W2 (sorts 1) [] [0, 0] []
            cap = HG.unsafeOpenHypergraph @_ @W2 @'[] (sorts 1) [0, 0] [] []
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
        let graph = spider @W2 @W1 Z (1 / 4)
        checkGraphLikeNormalisation graph
        case normaliseGraphLike graph of
          Left err -> testFailed err
          Right normal -> checkMatrix normal (matrixEntries (ZX.zSpider (pi / 4) :: ZX.ZX 2 1))
    , testProperty "implicit fan-out, states and discards become explicit spiders" $ do
        let copy = HG.unsafeOpenHypergraph @_ @W1 @W2 (sorts 1) [0] [0, 0] []
            state = HG.unsafeOpenHypergraph @_ @'[] @W1 (sorts 1) [] [0] []
            discard = HG.unsafeOpenHypergraph @_ @W1 @'[] (sorts 1) [0] [] []
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

checkAutomaticSimplification :: (a :: Diagram) ~> b -> Property ()
checkAutomaticSimplification diagram = do
  (steps, result) <- either testFailed pure (simplify diagram)
  check "graph-like result" (graphLike result)
  expect "remaining local-complementation candidates" [] (localComplementCandidates result)
  expect "remaining pivot candidates" [] (pivotCandidates result)
  expect "remaining gadget pivots" [] (gadgetPivotCandidates result)
  check "remaining gadget reductions" (case gadgetReduction result of Nothing -> True; Just _ -> False)
  check "nonnegative step count" (steps >= 0)
  either testFailed (checkMatrix result) (matrix diagram)
  (again, stable) <- either testFailed pure (simplify result)
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
        let copy = HG.unsafeOpenHypergraph @_ @W1 @W2 (sorts 1) [0] [0, 0] []
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
    , testProperty "an isolated Pauli pi spider absorbs scalar factors" $
        case openGraph 1 [1 / 2, 1 / 4, 0, 1] [(0, 1)] of
          HG.SomeHypergraph graph -> do
            checkAutomaticSimplification graph
            case simplify graph of
              Left err -> testFailed err
              Right (steps, result) -> do
                expect "no applicable rule" 0 steps
                let (_, _, _, boxes) = HG.hypergraphParts result
                expect "the boundary phases and exact zero remain" [1 / 4, 1 / 2, 1] (sort [a | HG.Box (Spider Z a) _ _ <- boxes])
                expect "the factor of two is absorbed by exact zero" (0, 0) (scalarFactors result)
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
        gates <- either testFailed pure (cnotHadPhaseCircuit qubits depth seed)
        circuit <- either testFailed pure (circuitDiagram qubits gates)
        case circuit of
          HG.SomeHypergraph graph -> do
            let expected = circuitMatrix qubits gates
            checkMatrix graph expected
            (_, result) <- either testFailed pure (simplify graph)
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
        let copy = HG.unsafeOpenHypergraph @_ @W1 @W2 (sorts 1) [0] [0, 0] []
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
    , testProperty "learned Hadamard loop cleanup adds pi and retains inverse sqrt two" $ do
        mapM_
          ( \p -> case openGraph 1 [p] [(0, 0)] of
              HG.SomeHypergraph graph -> do
                after <- checkedOptimisation graph
                expect "phase correction" (Just ([phase (p + 1)], [])) (boundaryGraph after)
                expect "scalar correction" (-1, 0) (scalarFactors after)
          )
          [0, 1 / 4, 1, 5 / 7]
        mapM_
          ( \ends -> do
              let source =
                    HG.unsafeOpenHypergraph @_ @HG.W3 @'[]
                      (sorts 5)
                      [2, 3, 4]
                      []
                      [HG.Box (Spider Z (1 / 4)) [] [2, 0, 3, 1, 4], HG.Box Hadamard [] ends]
              after <- checkedOptimisation source
              let (_, boundary, _, boxes) = HG.hypergraphParts after
              case [(p, legs) | HG.Box (Spider Z p) [] legs <- boxes] of
                [(p, legs)] -> expect "the shifted spider keeps all three external legs" (5 / 4, sort boundary) (p, sort legs)
                _ -> testFailed "expected one green spider after removing the loop"
              expect "scalar correction" (-1, 0) (scalarFactors after)
          )
          [[0, 1], [1, 0]]
    , testProperty "selection rejects boundaries, non-Clifford phases and non-simple graphs" $ do
        case openGraph 1 [1 / 2, 1 / 4] [(0, 1)] of
          HG.SomeHypergraph graph -> do
            check "boundary selected" (isLeft (localComplementAt 0 graph))
            check "non-Clifford selected" (isLeft (localComplementAt 1 graph))
            check "missing vertex selected" (isLeft (localComplementAt 999 graph))
        case openGraph 1 [1 / 4, 1 / 2] [(0, 1), (0, 1)] of
          HG.SomeHypergraph graph -> check "parallel input accepted" (isLeft (localComplementAt 1 graph))
    ]

checkOptimisation :: (a :: Diagram) ~> b -> Property ()
checkOptimisation = void . checkedOptimisation

checkedOptimisation
  :: (a :: Diagram) ~> b -> Property (HG.Wires (HG.WireSorts a) ~> (HG.Wires (HG.WireSorts b) :: Diagram))
checkedOptimisation graph = do
  (steps, after) <- either testFailed pure (optimise graph)
  check "rewrites applied" (steps > 0)
  either testFailed (checkMatrix after) (matrix graph)
  (n, stable) <- either testFailed pure (optimise after)
  expect "fixed point" 0 n
  check "stable graph" (HG.isomorphic after stable)
  pure after

beforeMatrix :: ZX.ZX 2 2
beforeMatrix =
  (ZX.zSpider @1 @1 (pi / 4) ** ZX.hadamard @1)
    . (ZX.zSpider @1 @1 (-(pi / 4)) ** ZX.hadamard @1)
    . ZX.cnot
    . ((ZX.hadamard @1 . ZX.xSpider (pi / 4) . ZX.hadamard @1) ** obj @1)

test :: TestTree
test =
  testGroup "ZX rewriting" $
    [ pivotCongruenceTests
    , generatedCircuitTests
    , boundaryPivotTests
    , gadgetTests
    , pivotTests
    , automaticTests
    , graphLikeTests
    , localComplementTests
    ]
      ++ overlapTests
      ++ cleanupTests

cleanupTests :: [TestTree]
cleanupTests =
  [ testProperty "the worked circuit simplifies and preserves its matrix including scalars" $ do
      checkMatrix before (matrixEntries beforeMatrix)
      after <- checkedOptimisation before
      checkGraphLikeNormalisation before
      check "fewer generators" (boxCount after < boxCount before)
  , testProperty "exact rational phases fuse modulo two, including newly created phases" $ do
      let graph = z (1 / 3) . z (1 / 5) . z (22 / 15)
      after <- checkedOptimisation graph
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
            HG.unsafeOpenHypergraph @_ @'[] @W5
              (sorts 7)
              []
              [2, 3, 4, 5, 6]
              [HG.Box (Spider Z (1 / 3)) [] [0, 3, 4], HG.Box (Spider Z (1 / 5)) [] [0, 1, 5], HG.Box (Spider Z (1 / 7)) [] [1, 2, 6]]
      after <- checkedOptimisation graph
      expect "one degree-five spider" 1 (boxCount after)
      checkMatrix after (matrixEntries (ZX.zSpider (pi * (1 / 3 + 1 / 5 + 1 / 7)) :: ZX.ZX 0 5))
  , testProperty "colour change and Hadamard cancellation implement H-X-H = Z" $ do
      p <- Falsify.gen (Gen.elem (0 :| [1 / 4, -(1 / 3), 5 / 7]))
      let graph = h . x p . h
      checkMatrix graph (matrixEntries (ZX.zSpider (pi * fromRational p) :: ZX.ZX 1 1))
      after <- checkedOptimisation graph
      let (_, _, _, boxes) = HG.hypergraphParts after
      expect "only a Z phase remains" [Spider Z (phase p) | phase p /= 0] (map HG.label boxes)
  , testProperty "independent rules are applied in the same compiled batch" $ do
      let graph = (z (1 / 3) . z (1 / 5)) ** (h . h)
          (ns, is, os, boxes) = HG.hypergraphParts graph
          states = map stateBox boxes
      case rules of
        Left err -> testFailed err
        Right compiled -> do
          let (n, after) = R.rewriteBatchCompiled compiled (HG.unsafeOpenHypergraph @_ @W2 @W2 ns is os states)
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
      let cup = HG.unsafeOpenHypergraph @_ @'[] @W2 (sorts 1) [] [0, 0] []
          scalar = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] []
      checkMatrix cup (matrixEntries (ZX.zSpider 0 :: ZX.ZX 0 2))
      checkMatrix scalar (Map.singleton (0, 0) 2)
  ]
