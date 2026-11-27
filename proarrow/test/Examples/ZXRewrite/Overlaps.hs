-- | Symbolic phase and wiring checks for overlaps of the ZX cleanup rules.
module Examples.ZXRewrite.Overlaps (cleanupOverlapReport, overlapTests) where

import Control.Monad (replicateM)
import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List (find, mapAccumL, sort)
import Data.Map.Strict qualified as Map
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((.))

import Examples.ZXRewrite.Diagram
import Examples.ZXRewrite.Rules
import Examples.ZXRewrite.Simplify
import Proarrow.Category.Instance.OpenHypergraph (W2)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion

checkVariadicFusionFork :: Property ()
checkVariadicFusionFork = do
  let spiderBox = HG.Box (Spider Z (0 :: Rational))
      a = R.Capture "a"
      b = R.Capture "b"
      c = R.Capture "c"
      d = R.Capture "d"
      e = R.Capture "e"
      f = R.Capture "f"
      link = R.Node 0
  -- Splice each port list at the shared wire, keeping the order on both sides.
  fuse <-
    either testFailed pure $
      R.portRule
        (R.PortGraph (sorts 1) [] [spiderBox [a] [b, link, c], spiderBox [d, link, e] [f]])
        (R.PortGraph [] [] [spiderBox [d, a, e] [b, f, c]])
  templates <- either testFailed pure (Completion.portOverlapTemplates [fuse])
  let numbered = any \case R.Node _ -> True; _ -> False
  template <- case [ source
                   | source@(R.PortGraph _ _ boxes@[_, _, _]) <- templates
                   , any (\b' -> numbered (HG.inputs b') && numbered (HG.outputs b')) boxes
                   ] of
    [source] -> pure source
    _ -> testFailed "expected one generated three-spider overlap"
  let fusionRules = [("fusion", fuse)]
  shallow <- either testFailed pure (Completion.checkPortTemplate (Just 0) fusionRules template)
  case shallow of
    Completion.PortTemplateJoinLimit (Completion.CriticalOverlap "fusion" "fusion" host _ _) -> do
      let (_, ins, _, _) = HG.hypergraphParts host
      expect "one protected boundary point per sequence" 10 (length ins)
    _ -> testFailed "the symbolic branches require one more fusion"
  result <- either testFailed pure (Completion.checkPortTemplate (Just 1) fusionRules template)
  case result of
    Completion.PortTemplateJoinable count -> expect "one symbolic fusion fork" 1 count
    _ -> testFailed "the symbolic fusion fork should join"
  compiled <- either testFailed pure (R.compileReducingRules fusionRules)
  let checkConcrete segments = case segments of
        [as, bs, cs, ds, es, fs] -> do
          let boundary = nubOrd (concat segments)
              n = maximum (1 : boundary) + 1
              boxes = [spiderBox as (bs ++ [0]), spiderBox (0 : cs) (ds ++ [1]), spiderBox (1 : es) fs]
          case someDiagram n boundary [] boxes of
            HG.SomeHypergraph host -> case R.rewritesCompiled compiled host of
              [(_, left), (_, right)] -> do
                let l = R.normalise R.unlimitedRewrites compiled left
                    r = R.normalise R.unlimitedRewrites compiled right
                expect "one more fusion on each side" (1, 1) (R.normalisationRewrites l, R.normalisationRewrites r)
                check "the concrete fusion fork joins" (HG.isomorphic (R.normalisedGraph l) (R.normalisedGraph r))
              _ -> testFailed "expected two directed fusions"
        _ -> testFailed "expected six leg sequences"
      allocate start len = (start + len, take len [start ..])
  mapM_ (checkConcrete . snd . mapAccumL allocate 2) (replicateM 6 [0 .. 2])
  checkConcrete [[2, 2], [], [2, 3], [3], [], [3, 2]]

data PhaseStage a = PhaseStage Char a | PhaseConnector
  deriving (Eq, Show, Functor, Foldable, Traversable)

checkPhaseCompletion :: Property ()
checkPhaseCompletion = do
  let incoming = R.Capture "incoming"
      outgoing = R.Capture "outgoing"
      alpha = R.Variable "alpha"
      beta = R.Variable "beta"
      first = HG.Box (PhaseStage 'a' alpha) [incoming] [R.Node 0]
      middle = HG.Box PhaseConnector [R.Node 0] [R.Node 1]
      lastBox = HG.Box (PhaseStage 'c' beta) [R.Node 1] [outgoing]
      joined angle = HG.Box (PhaseStage 't' angle) [incoming] [outgoing]
      prefix :: (Eq a) => Either String (R.Rule () (PhaseStage a))
      prefix =
        R.parameterPortRule
          (portDiagram [1] [first, middle])
          (portDiagram [0] [HG.Box (PhaseStage 'd' alpha) [incoming] [R.Node 0]])
      whole :: (Eq a) => (a -> a -> a) -> Either String (R.Rule () (PhaseStage a))
      whole add = R.parameterPortRule (closedPorts [first, middle, lastBox]) (closedPorts [joined (R.zipParameters add alpha beta)])
      order (R.PortGraph _ _ l) (R.PortGraph _ _ r) = compare (length l) (length r)
  symbolic <- either testFailed pure (sequence [prefix, whole addPhaseSums])
  templates <- either testFailed pure (Completion.parameterPortOverlapTemplates phaseVariable symbolic)
  source <- case templates of
    [template] -> pure template
    _ -> testFailed "expected one symbolic phase-labelled fork"
  let named = zip [0 :: Int ..] symbolic
  fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) named source)
  symbolicRule <-
    either testFailed pure (Completion.orientParameterPortOverlap symbolicPhaseParameter order source fork)
  joinedFork <- either testFailed pure (Completion.checkPortTemplate (Just 1) (named ++ [(2, symbolicRule)]) source)
  case joinedFork of
    Completion.PortTemplateJoinable count -> expect "the two symbolic phase expressions agree" 1 count
    _ -> testFailed "expected the learned rule to close the symbolic fork"
  let add a b = phase (a + b)
  concrete <- either testFailed pure (sequence [prefix, whole add])
  seeds <- either testFailed pure (R.compileReducingRules (zip [0 :: Int ..] concrete))
  learned <- either testFailed pure (Completion.orientParameterPortOverlap rationalPhaseParameter order source fork)
  let samples = [(1 / 4, 1 / 2, 3 / 4), (3 / 2, 3 / 4, 1 / 4), (2 / 3, 2 / 3, 4 / 3)]
  mapM_ (checkConcrete seeds learned) samples
  let prefixed = HG.Box (PhaseStage 'd' alpha) [R.Node 0] [R.Node 1]
      finished = HG.Box (PhaseStage 't' alpha) [R.Node 0] [outgoing]
      extra zero =
        let start = HG.Box (PhaseStage 'x' (R.Literal zero)) [incoming] [R.Node 0]
        in sequence
             [ R.parameterPortRule
                 (portDiagram [1] [start, prefixed])
                 (portDiagram [0] [HG.Box (PhaseStage 'y' alpha) [incoming] [R.Node 0]])
             , R.parameterPortRule
                 (closedPorts [start, finished])
                 (closedPorts [HG.Box (PhaseStage 'v' alpha) [incoming] [outgoing]])
             ]
  symbolicExtra <- either testFailed pure (extra (phaseConstant 0))
  concreteExtra <- either testFailed pure (extra 0)
  let complete budget =
        Completion.completeParameterPorts
          (Completion.parameterPortOptions phaseVariable symbolicPhaseParameter rationalPhaseParameter)
          (Completion.PortCompletionOptions budget 2 order)
          (symbolic ++ symbolicExtra)
  (firstRound, partial) <- either testFailed pure (complete 1)
  case firstRound of
    Completion.PortIncomplete retained (Completion.PortRuleLimit _ (Completion.CriticalOverlap 2 4 _ _ _)) -> do
      expect "the first learned phase rule creates a new fork" 5 (length retained)
      expect "a bounded stop still emits the learned concrete rule" 1 (length partial)
    _ -> testFailed "expected the phase-labelled fork with the first learned rule"
  (secondRound, emitted) <- either testFailed pure (complete 2)
  case secondRound of
    Completion.PortComplete completed _ -> do
      expect "completion learns two phase rules" 6 (length completed)
      expect "both learned rules are emitted for rational phases" 2 (length emitted)
      compiled <- either testFailed pure (R.compileReducingRules (zip [0 :: Int ..] (concrete ++ concreteExtra ++ emitted)))
      mapM_ (checkSecondRound compiled) samples
    _ -> testFailed "expected both phase-labelled forks to close"
  where
    checkConcrete seeds learned (a, b, expectedPhase) = do
      let host =
            HG.unsafeOpenHypergraph @_ @W2 @'[]
              (sorts 4)
              [2, 3]
              []
              [HG.Box (PhaseStage 'a' a) [2, 3, 2] [0], HG.Box PhaseConnector [0] [1], HG.Box (PhaseStage 'c' b) [1] [3, 3]]
          expected = HG.unsafeOpenHypergraph @_ @W2 @'[] (sorts 2) [0, 1] [] [HG.Box (PhaseStage 't' expectedPhase) [0, 1, 0] [1, 1]]
      case R.rewritesCompiled seeds host of
        [(0, l), (1, r)] -> case R.rewrites learned l of
          [target] -> do
            check "the learned rule agrees with direct contraction" (HG.isomorphic target r)
            check "concrete phases add modulo two and captured ports survive" (HG.isomorphic target expected)
          _ -> testFailed "expected the learned phase rule to match the residual chain"
        _ -> testFailed "expected one concrete match for each seed rule"
    checkSecondRound compiled (a, b, expectedPhase) = do
      let host =
            HG.unsafeOpenHypergraph @_ @W2 @'[]
              (sorts 5)
              [3, 4]
              []
              [ HG.Box (PhaseStage 'x' 0) [3, 4, 3] [0]
              , HG.Box (PhaseStage 'a' a) [0] [1]
              , HG.Box PhaseConnector [1] [2]
              , HG.Box (PhaseStage 'c' b) [2] [4, 4]
              ]
      (firstBranch, otherBranch) <- case R.rewritesCompiled compiled host of
        [(0, l), (1, r)] -> pure (l, r)
        _ -> testFailed "expected both seed contractions on the extended chain"
      (residual, learnedFirst) <- case R.rewritesCompiled compiled firstBranch of
        [(2, l), (4, r)] -> pure (l, r)
        _ -> testFailed "expected a seed rule and the first emitted rule on the new fork"
      target <- case R.rewritesCompiled compiled residual of
        [(5, result)] -> pure result
        _ -> testFailed "expected the second learned rule on the residual chain"
      let expected =
            HG.unsafeOpenHypergraph @_ @W2 @'[]
              (sorts 2)
              [0, 1]
              []
              [HG.Box (PhaseStage 'v' expectedPhase) [0, 1, 0] [1, 1]]
          normalise = R.normalisedGraph . R.normalise R.unlimitedRewrites compiled
      check "the second learned rule retains the sum and captured ports" (HG.isomorphic target expected)
      check "all completed paths agree" (all (HG.isomorphic target . normalise) [learnedFirst, otherBranch])

symbolicFusionRule :: Colour -> Either String (R.Rule () (Generator PhaseSum))
symbolicFusionRule = spiderFusionRule addPhaseSums

symbolicPortOverlaps :: [R.Rule () (Generator PhaseSum)] -> Either String [R.PortGraph () (Generator PhaseSum)]
symbolicPortOverlaps = Completion.parameterPortOverlapTemplates phaseVariable

checkSpiderCleanupOverlaps :: Property ()
checkSpiderCleanupOverlaps = mapM_ checkColour [Z, X]
  where
    checkColour c = do
      fuse <- either testFailed pure (symbolicFusionRule c)
      loop <- either testFailed pure (spiderLoopRule c)
      identity <- either testFailed pure (spiderIdentityRule (phaseConstant 0) c)
      let checks = [("fusion", fuse), ("loop", loop), ("identity", identity)]
      templates <- either testFailed pure (symbolicPortOverlaps (map snd checks))
      expect "spider overlap shapes" expectedShapes (sort (nubOrd (map templateShape templates)))
      let loopOrders = [[n | R.Node n <- ps] | R.PortGraph [_, _] [] [HG.Box _ [] ps] <- templates]
      expect "separate, interleaved and nested loop endpoints" loopEndpoints (sort loopOrders)
      mapM_ (checkJoin checks) templates
      checkPhaseSum checks templates
    templateShape (R.PortGraph ns boundary boxes) = (length ns, length boundary, length boxes)
    expectedShapes = [(1, 0, 2), (2, 0, 1), (2, 0, 2), (2, 0, 3), (2, 1, 2), (2, 2, 2)]
    loopEndpoints = [[0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]]
    checkJoin checks source = do
      -- Removing two loops preserves exact leg order. Fusion can permute legs.
      let comparePorts
            | templateShape source == (2, 0, 1) = Completion.checkPortTemplate
            | otherwise = Completion.checkPortTemplateWithSymmetry zxPortSymmetry
      joined <- either testFailed pure (comparePorts (Just 1) checks source)
      case joined of
        Completion.PortTemplateJoinable count -> check "the generated fork has two joining steps" (count > 0)
        _ -> testFailed "expected the spider cleanup fork to join up to leg order"
    checkPhaseSum checks templates = do
      source <-
        maybe (testFailed "expected a three-spider fusion overlap") pure (find ((== (2, 0, 3)) . templateShape) templates)
      exact <- either testFailed pure (Completion.checkPortTemplate (Just 1) checks source)
      case exact of
        Completion.PortTemplateUnjoinable (Completion.CriticalOverlap "fusion" "fusion" _ left right) -> do
          compiled <- either testFailed pure (R.compileRules (zip [0 :: Int ..] (map snd checks)))
          mapM_ (checkFused . R.normalisedGraph . R.normalise R.unlimitedRewrites compiled) [left, right]
        _ -> testFailed "expected an ordered fusion fork to differ by leg order"
    checkFused diagram = case HG.hypergraphParts diagram of
      (_, ins, [], [HG.Box (Spider _ (PhaseSum offset summed)) [] legs]) -> do
        expect "each original phase contributes once" (0, [1, 1, 1]) (offset, IM.elems summed)
        expect "all seven leg sequences survive in the fused spider" (7, sort ins) (length ins, sort legs)
      _ -> testFailed "expected one fused spider with all the original legs"

checkSequenceMarkers :: Property ()
checkSequenceMarkers = do
  fuse <- either testFailed pure (symbolicFusionRule Z)
  identity <- either testFailed pure (spiderIdentityRule (phaseConstant 0) Z)
  let link = R.Node 0
      source =
        R.PortGraph
          (sorts 1)
          []
          [ HG.Box (Spider Z (phaseConstant 0)) [] [link, R.Capture "legs"]
          , HG.Box (Spider Z (phaseVariable 0)) [] [R.Capture "before", link, R.Capture "after"]
          ]
  result <-
    either testFailed pure $
      Completion.checkPortTemplateWithSymmetry zxPortSymmetry (Just 0) [((), fuse), ((), identity)] source
  case result of
    Completion.PortTemplateJoinable count -> expect "only the two fusion orientations match" 1 count
    _ -> testFailed "expected fusion without binding a sequence marker to an interface node"

parallelIdentityHost
  :: R.PortGraph () (Generator a)
  -> Property ((HG.Wires W2 :: HG.OPENHG () (Generator a)) ~> HG.Wires '[])
parallelIdentityHost source = case source of
  R.PortGraph ns boundary@[_, _] [HG.Box a [] [R.Node p, R.Node q], HG.Box b [] [R.Node r, R.Node s]] ->
    pure (HG.unsafeOpenHypergraph ns boundary [] [HG.Box a [] [p, q], HG.Box b [] [r, s]])
  _ -> testFailed "expected both bivalent spiders to use the same two numbered wires"

checkMixedParallelIdentities :: Property ()
checkMixedParallelIdentities = do
  green <- either testFailed pure (spiderIdentityRule (0 :: Rational) Z)
  red <- either testFailed pure (spiderIdentityRule 0 X)
  templates <- either testFailed pure (Completion.parameterPortOverlapTemplates (fromIntegral . (+ 1)) [green, red])
  let mixed =
        [ source
        | source@(R.PortGraph _ _ [HG.Box (Spider Z 0) _ _, HG.Box (Spider X 0) _ _]) <- templates
        ]
  expect "both orders of the shared wires for mixed colours" 2 (length mixed)
  identities <- either testFailed pure (R.compileRules [(Z, green), (X, red)])
  cleanup <- either testFailed pure rules
  mapM_ (checkSource identities cleanup) mixed
  where
    checkSource identities cleanup source = do
      host <- parallelIdentityHost source
      case R.rewritesCompiled identities host of
        [(Z, redLoop), (X, greenLoop)] -> do
          (openRed, openGreen) <- checkOpen cleanup redLoop greenLoop
          expected <- either testFailed pure (matrix host)
          checkMatrix openRed expected
          checkMatrix openGreen expected
          let closed branch =
                let (ns, _, _, boxes) = HG.hypergraphParts branch
                in HG.unsafeOpenHypergraph @_ @'[] @'[] ns [] [] boxes
              normal = R.normalisedGraph . R.normalise R.unlimitedRewrites cleanup . closed
              closedRed = normal redLoop
              closedGreen = normal greenLoop
          check "closing the boundary lets cleanup join the branches" (HG.isomorphic closedRed closedGreen)
          expect "both branches reduce to a scalar green spider" [HG.Box (Spider Z 0) [] []] (diagramBoxes closedGreen)
          checkMatrix closedRed (Map.singleton (0, 0) 2)
        _ -> testFailed "expected one first step for each identity colour"
    checkOpen cleanup redLoop greenLoop = do
      expanded <- oneStep cleanup redLoop
      expect
        "colour change adds a Hadamard on each leg"
        [Spider Z 0, Hadamard, Hadamard]
        (sort (map HG.label (diagramBoxes expanded)))
      pair <- oneStep cleanup expanded
      case HG.hypergraphParts pair of
        (ns, boundary, [], [HG.Box Hadamard [] a, HG.Box Hadamard [] b]) -> do
          let orientations =
                [ [HG.Box Hadamard [] first, HG.Box Hadamard [] second]
                | first <- [a, reverse a]
                , second <- [b, reverse b]
                ]
              withBoundary input boxes = HG.unsafeOpenHypergraph @_ @W2 @'[] ns input [] boxes
              checkContraction boxes = do
                let matches = R.rewritesCompiled cleanup (withBoundary boundary boxes)
                check "the pair contracts with one exposed wire" (not (null matches))
                mapM_ (check "every contraction reaches the green self-loop" . HG.isomorphic greenLoop . snd) matches
                let bothExposed = withBoundary a boxes
                expect "both exposed wires are preserved" 0 (length (R.rewritesCompiled cleanup bothExposed))
          mapM_ checkContraction orientations
        _ -> testFailed "expected identity removal to leave two parallel Hadamards"
      let joined = R.normalisedGraph (R.normalise R.unlimitedRewrites cleanup pair)
      expect "the green self-loop is irreducible at the boundary" 0 (length (R.rewritesCompiled cleanup greenLoop))
      check "the open branches join" (HG.isomorphic joined greenLoop)
      pure (joined, greenLoop)
    oneStep cleanup graph = case R.rewritesCompiled cleanup graph of
      [(_, result)] -> pure result
      _ -> testFailed "expected exactly one available cleanup step"
    diagramBoxes graph = let (_, _, _, boxes) = HG.hypergraphParts graph in boxes

parallelHadamardRules :: (Eq a) => a -> Either String [(String, R.Rule () (Generator a))]
parallelHadamardRules zero = do
  closed <-
    traverse
      (fmap ("closed",))
      [closedPorts [hadamardPorts (0, 1), hadamardPorts b] ==> closedPorts [green []] | b <- wireOrders 0 1]
  -- Each squared entry is 1/2. Summing the internal wire leaves weight 1
  -- on the retained wire, represented by a green self-loop.
  retained <-
    hadamardVariants "retain wire" $
      portDiagram [0] [hadamardPorts (0, 1), hadamardPorts (0, 1)] ==> portDiagram [0] [green [R.Node 0, R.Node 0]]
  pure (closed ++ retained)
  where
    green = spiderWithPorts Z (R.Literal zero)

-- Reference equations used as targets in the recovery tests.
referenceCleanupRules :: Either String [(String, R.Rule () (Generator PhaseSum))]
referenceCleanupRules = do
  attached <- map ("Hadamard loop",) . fst <$> completedAttachedHadamardLoops
  trace <- closedPorts [hadamardPorts (0, 0)] ==> closedPorts [spiderWithPorts Z (R.Literal (phaseConstant 1)) []]
  series <-
    hadamardVariants "Hadamard chain" $
      portDiagram [0, 2] [hadamardPorts (0, 1), hadamardPorts (1, 2)] ==> portDiagram [0, 0] []
  parallel <- parallelHadamardRules (phaseConstant 0)
  betweenSpiders <- map ("parallel Hadamard edges",) . fst <$> completedParallelHadamardEdges
  fixedCleanupRules
    True
    (phaseConstant 0)
    addPhaseSums
    (attached ++ [("Hadamard loop", trace)] ++ betweenSpiders ++ series ++ parallel)

checkParallelHadamardCompletion :: Property ()
checkParallelHadamardCompletion = do
  (_, learned) <- either testFailed pure completedParallelHadamardEdges
  expect "completion emits eight ordered variants" 8 (length learned)
  compiled <- either testFailed pure (R.compileRules (zip [0 :: Int ..] learned))
  let alpha = 1 / 4
      beta = 1 / 3
      green angle = HG.Box (Spider Z angle) []
      cases =
        [ HG.unsafeOpenHypergraph @_ @W2 @'[]
            (sorts 6)
            [4, 5]
            []
            [ green alpha [0, 4, 2, 4]
            , green beta [5, first, second]
            , HG.Box Hadamard [] [a, b]
            , HG.Box Hadamard [] [c, d]
            ]
        | (first, second) <- wireOrders 1 3
        , (a, b) <- wireOrders 0 1
        , (c, d) <- wireOrders 2 3
        ]
      expected =
        HG.unsafeOpenHypergraph @_ @W2 @'[]
          (sorts 2)
          [0, 1]
          []
          [green alpha [0, 0], green beta [1], HG.Box (Scalar (-2) 0) [] []]
  mapM_
    ( \source -> do
        original <- either testFailed pure (matrix source)
        let targets = map snd (R.rewritesCompiled compiled source)
        check "a learned rule matches this port ordering" (not (null targets))
        mapM_
          (\target -> check "the rule cancels the parallel edges" (HG.isomorphic target expected) >> checkMatrix target original)
          targets
        (_, after) <- either testFailed pure (optimise source)
        check "cleanup uses the learned cancellation" (HG.isomorphic after expected)
    )
    cases

checkHadamardLoopCompletion :: Property ()
checkHadamardLoopCompletion = do
  (parallelRules, _) <- either testFailed pure completedParallelHadamardEdges
  parallel <- case parallelRules of
    r : _ -> pure r
    [] -> testFailed "expected a parallel Hadamard rule"
  fuse <- either testFailed pure (symbolicFusionRule Z)
  let seeds = [parallel, fuse]
      alpha = phaseVariable 0
      beta = phaseVariable 1
      sumAB = addPhaseSums alpha beta
  expect "visible phases keep the sum constrained" sumAB (reparameterisePhases [alpha, beta, sumAB] [sumAB] sumAB)
  original <-
    either testFailed pure $
      Completion.completeParameterPorts
        zxPortParameters
        (Completion.PortCompletionOptions 1 4 zxCompletionOrder)
        seeds
  fork <- case original of
    (Completion.PortIncomplete _ (Completion.PortUnorientable message _ witness), []) -> do
      expect "the unchanged phase sum cannot appear on the left" "parameterRule: computed expression on the left" message
      pure witness
    _ -> testFailed "expected the phase expression to prevent orientation"
  let recover matchingSymmetry budget =
        either testFailed pure $
          Completion.completeParameterPorts
            zxHadamardParameters{Completion.matchingPortSymmetry = matchingSymmetry}
            (Completion.PortCompletionOptions budget 4 zxCompletionOrder)
            seeds
  (completion, recovered) <- recover (const R.OrderedPorts) 2
  (eliminateLoops, rearrangeCaptures) <- case recovered of
    [first, second] -> pure (first, second)
    _ -> testFailed "expected both port orderings of the two-loop rule"
  let completed = case completion of
        Completion.PortComplete rs _ -> rs
        Completion.PortIncomplete rs _ -> rs
  compiled <- either testFailed pure (R.compileRules (zip [0 :: Int ..] completed))
  case fork of
    Completion.CriticalOverlap _ _ _ left right -> do
      -- All numbered ports of these rules are internal. The matcher cannot
      -- select a sequence marker for one because it is a boundary input.
      let normalise = R.normalisedGraph . R.normalise R.unlimitedRewrites compiled
      check "the learned rule joins the original symbolic fork" (HG.isomorphic (normalise left) (normalise right))
  let cases = [(0, ([], [], [], [], [])), (1 / 3, ([4], [5], [], [], [])), (7 / 4, ([], [4, 4], [5, 4], [], [5]))]
  mapM_ (checkMatrixAfter (R.rewrites eliminateLoops) ([0, 2], [1, 3]) False) cases
  mapM_ (checkMatrixAfter (R.rewrites rearrangeCaptures) ([2, 0], [3, 1]) True) cases
  (withVariants, variants) <- recover hadamardSymmetry 1
  expect "one learned equation emits all four Hadamard variants" 4 (length variants)
  let retained = case withVariants of
        Completion.PortComplete rs _ -> rs
        Completion.PortIncomplete rs _ -> rs
  expect "all variants are available to the overlap search" (length seeds + 4) (length retained)
  compiledVariants <- either testFailed pure (R.compileRules (zip [0 :: Int ..] variants))
  let rewrite = map snd . R.rewritesCompiled compiledVariants
  mapM_
    (\ends -> mapM_ (checkMatrixAfter rewrite ends False) cases)
    [(first, second) | first <- [[0, 2], [2, 0]], second <- [[1, 3], [3, 1]]]
  where
    checkMatrixAfter rewrite (first, second) rearranged (angle, (a, b, c, d, e)) = do
      let captured = if rearranged then c ++ d ++ e ++ a ++ b else a ++ b ++ c ++ d ++ e
          source =
            HG.unsafeOpenHypergraph @_ @W2 @'[]
              (sorts 6)
              [4, 5]
              []
              [ HG.Box Hadamard [] first
              , HG.Box Hadamard [] second
              , HG.Box (Spider Z angle) [] (a ++ [0] ++ b ++ [1] ++ c ++ [2] ++ d ++ [3] ++ e)
              ]
          expected =
            HG.unsafeOpenHypergraph @_ @W2 @'[]
              (sorts 2)
              [0, 1]
              []
              [HG.Box (Scalar (-2) 0) [] [], HG.Box (Spider Z angle) [] (map (subtract 4) captured)]
          targets = rewrite source
      check "the abstract phase matches with arbitrary captured legs" (not (null targets))
      originalMatrix <- either testFailed pure (matrix source)
      mapM_
        ( \target -> do
            check "the rule returns the original phase with factor one half" (HG.isomorphic target expected)
            checkMatrix target originalMatrix
        )
        targets

-- Run on demand in GHCi. Generate and check overlaps of the cleanup rules,
-- including colour change on symbolic legs.
-- Count joined templates, then templates grouped by their first unjoinable
-- fork, then templates that hit the search bound.
cleanupOverlapReport :: Either String (Int, Map.Map [String] Int, Int)
cleanupOverlapReport = do
  fixed <- learnedSymbolicCleanupRules
  colour <- colourChangeRule
  let checks = fixed ++ [("colour change", colour)]
  templates <- symbolicPortOverlaps (map snd checks)
  results <-
    traverse
      ( Completion.checkPortTemplateWithScalars
          zxPortSymmetry
          symbolicScalar
          (Just 4)
          checks
      )
      templates
  let joined = length [() | Completion.PortTemplateJoinable _ <- results]
      blocked =
        Map.fromListWith
          (+)
          [ (sort [left, right], 1 :: Int)
          | result <- results
          , Completion.CriticalOverlap left right _ _ _ <- unjoinable result
          ]
      unjoinable (Completion.PortTemplateUnjoinable fork) = [fork]
      unjoinable (Completion.PortTemplateMappedUnjoinable (Completion.MappedPortFork fork _ _)) = [fork]
      unjoinable _ = []
      limited = length [() | result <- results, hitLimit result]
      hitLimit Completion.PortTemplateJoinLimit{} = True
      hitLimit Completion.PortTemplateMappedJoinLimit{} = True
      hitLimit _ = False
  pure (joined, blocked, limited)

checkColourChangeFusion :: Property ()
checkColourChangeFusion = do
  fixed <- either testFailed pure learnedSymbolicCleanupRules
  colour <- either testFailed pure colourChangeRule
  let checks = fixed ++ [("colour change", colour)]
      red n = spiderWithPorts X (phaseVariable n)
      link = R.Node 0
      first = red 0 [link]
      second = red 1 [R.Capture "a", link, R.Capture "b"]
  mapM_
    ( \boxes -> do
        result <-
          either testFailed pure $
            Completion.checkPortTemplateWithScalars zxPortSymmetry symbolicScalar (Just 4) checks (closedPorts boxes)
        case result of
          Completion.PortTemplateJoinable count -> check "colour change and fusion both apply" (count > 0)
          _ -> testFailed "expected colour change and fusion to join with opaque legs"
    )
    [[first, second], [second, first]]

checkHadamardLoopZero :: Property ()
checkHadamardLoopZero = do
  checks <- either testFailed pure referenceCleanupRules
  let ends = [R.Node 0, R.Node 1]
      identityBox = HG.Box (Spider Z (phaseConstant 0)) [] ends
      sources = [R.PortGraph (sorts 2) [] [identityBox, HG.Box Hadamard [] ports'] | ports' <- [ends, reverse ends]]
  mapM_ (checkFork checks) sources
  where
    checkFork checks source = do
      exact <- either testFailed pure (Completion.checkPortTemplateWithSymmetry zxPortSymmetry (Just 1) checks source)
      case exact of
        Completion.PortTemplateUnjoinable (Completion.CriticalOverlap "Hadamard loop" "identity" _ _ _) -> pure ()
        _ -> testFailed "expected a separate scalar factor on one branch"
      joined <-
        either testFailed pure $
          Completion.checkPortTemplateWithScalars zxPortSymmetry symbolicScalar (Just 1) checks source
      case joined of
        Completion.PortTemplateJoinable count -> check "the loop and identity reductions join at scalar zero" (count > 0)
        _ -> testFailed "expected zero to absorb the extra scalar factor"

checkHadamardTraceCompletion :: Property ()
checkHadamardTraceCompletion = do
  (variants, _) <- either testFailed pure completedAttachedHadamardLoops
  identity <- either testFailed pure (spiderIdentityRule (phaseConstant 0) Z)
  expect "one attached loop equation supplies both port orders" 2 (length variants)
  let seeds = variants ++ [identity]
      learn order = do
        result <-
          either testFailed pure $
            Completion.completeParameterPorts
              zxPortParameters
              (Completion.PortCompletionOptions 1 4 order)
              seeds
        case result of
          (Completion.PortComplete _ _, [r]) -> pure r
          _ -> testFailed "expected one learned equation for the closed trace"
      source = HG.unsafeOpenHypergraph @_ @'[] @'[] (sorts 1) [] [] [HG.Box Hadamard [] [0, 0]]
      zero = HG.unsafeOpenHypergraph @_ @'[] @'[] [] [] [] [HG.Box (Spider Z 1) [] [], HG.Box (Scalar (-1) 0) [] []]
  reverseRule <- learn zxCompletionOrder
  case R.rewrites reverseRule zero of
    [target] -> check "the box-count order prefers the single Hadamard box" (HG.isomorphic source target)
    _ -> testFailed "expected the equation in the reverse direction"
  traceRule <- learn zxHadamardCompletionOrder
  let checkZeroScalar graph = do
        let (_, _, _, boxes) = HG.hypergraphParts graph
        expect "exact zero absorbs the other scalar" [HG.Box (Spider Z 1) [] []] boxes
        checkMatrix graph (Map.singleton (0, 0) 0)
  case R.rewrites traceRule source of
    [target] -> do
      check "the Hadamard-first order reduces the trace to a scalar product" (HG.isomorphic zero target)
      checkZeroScalar (collectScalars target)
    _ -> testFailed "expected the closed Hadamard trace to reduce"
  (steps, simplified) <- either testFailed pure (optimise source)
  expect "ZX cleanup contracts the learned trace in one step" 1 steps
  checkZeroScalar simplified

checkCombinedHadamardCompletion :: Property ()
checkCombinedHadamardCompletion = do
  result <- either testFailed pure completeHadamardCleanup
  completed <- case result of
    (Completion.PortComplete rs _, emitted) -> do
      expect "three learned equations emit nine ordered rules" 9 (length emitted)
      expect "seed and learned variants make up the completed system" 15 (length rs)
      pure rs
    _ -> testFailed "expected five seed equations to close the Hadamard overlaps"
  fixed <- either testFailed pure referenceCleanupRules
  let targets = [(name, r) | (name, r) <- fixed, name `elem` ["Hadamard loop", "Hadamard chain", "closed", "retain wire"]]
  expect "the recovery check includes all thirteen variants" 13 (length targets)
  mapM_ (checkRecovered completed) targets
  where
    checkRecovered completed (name, r) = do
      -- The marker boxes protect the interface and opaque captures. Both
      -- fork steps remove the markers, leaving the completed rules to join
      -- the two sides of the target equation.
      (left@(R.PortGraph _ boundary boxes), right) <-
        either testFailed pure (R.parameterPortExample (const (phaseVariable 0)) r)
      let interface = [0 .. length boundary - 1]
          captures = nubOrd [capture | box <- boxes, R.Capture capture <- ports box]
          anchor = HG.Box (Pivot True (phaseConstant 0)) [] (map R.Node interface)
          marker i capture = HG.Box (Selected (phaseConstant (fromIntegral i))) [] [R.Capture capture]
          source = R.PortGraph (sorts (length interface)) interface (anchor : zipWith marker [0 :: Int ..] captures)
      toLeft <- either testFailed pure (R.portRule source left)
      toRight <- either testFailed pure (R.portRule source right)
      fork <-
        either testFailed pure $
          Completion.checkPortTemplateWithScalars
            zxPortSymmetry
            symbolicScalar
            (Just 4)
            (zip [0 :: Int ..] (toLeft : toRight : completed))
            source
      case fork of
        Completion.PortTemplateJoinable count -> expect ("the recovered fork joins for " ++ name) 1 count
        _ -> testFailed ("the completed rules should recover " ++ name)

checkHadamardChainSymmetry :: Property ()
checkHadamardChainSymmetry = do
  checks <- either testFailed pure referenceCleanupRules
  let hadamard a b = HG.Box Hadamard [] [R.Node a, R.Node b]
      source = R.PortGraph (sorts 4) [0, 3] [hadamard 0 1, hadamard 1 2, hadamard 3 2]
  exact <- either testFailed pure (Completion.checkPortTemplate (Just 0) checks source)
  case exact of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap "Hadamard chain" "Hadamard chain" _ _ _) -> pure ()
    _ -> testFailed "expected the two cancellations to leave opposite port orders"
  symmetric <- either testFailed pure (Completion.checkPortTemplateWithSymmetry zxPortSymmetry (Just 0) checks source)
  case symmetric of
    Completion.PortTemplateJoinable count -> check "both cancellations reach the same Hadamard" (count > 0)
    _ -> testFailed "expected Hadamard leg symmetry to join the fork"

checkHadamardChainIdentity :: Property ()
checkHadamardChainIdentity = do
  checks <- either testFailed pure referenceCleanupRules
  colour <- either testFailed pure colourChangeRule
  identity <- either testFailed pure (spiderIdentityRule (phaseConstant 0) X)
  templates <- either testFailed pure (symbolicPortOverlaps [identity, colour])
  case [source | source@(R.PortGraph _ [0, 1] [_]) <- templates] of
    [source] -> do
      result <- either testFailed pure (Completion.checkPortTemplate (Just 4) (checks ++ [("colour change", colour)]) source)
      case result of
        Completion.PortTemplateJoinable count -> check "colour change and red identity removal join" (count > 0)
        _ -> testFailed "expected colour change and red identity removal to join"
    _ -> testFailed "expected one red spider whose arity is fixed by the identity rule"
  let boxes = [HG.Box (Spider X 0) [] [0, 1], HG.Box Hadamard [] [0, 2], HG.Box Hadamard [] [2, 1]]
      source = R.PortGraph (sorts 3) [0, 1] (map (fmap R.Node . adaptPhase) boxes)
      adaptPhase (HG.Box label' ins outs) = HG.Box (fmap phaseConstant label') ins outs
      checkFork = Completion.checkPortTemplateWithScalars zxPortSymmetry symbolicScalar (Just 4)
  before <- either testFailed pure (checkFork checks source)
  case before of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap left right _ _ _) ->
      expect "the fixed rules get stuck on the red self-loop" ["Hadamard chain", "identity"] (sort [left, right])
    _ -> testFailed "expected the fixed rules to get stuck on the red self-loop"
  after <- either testFailed pure (checkFork (checks ++ [("colour change", colour)]) source)
  case after of
    Completion.PortTemplateJoinable count -> check "the chain and identity fork joins" (count > 0)
    _ -> testFailed "expected colour change to join the fork"
  let host = HG.unsafeOpenHypergraph @_ @W2 @'[] (sorts 3) [0, 1] [] boxes
  cleanup <- either testFailed pure rules
  expected <- either testFailed pure (matrix host)
  let firstSteps = map snd (R.rewritesCompiled cleanup host)
      greenLoop = HG.unsafeOpenHypergraph @_ @W2 @'[] (sorts 1) [0, 0] [] [HG.Box (Spider Z 0) [] [0, 0]]
  targets <- traverse (either testFailed (pure . snd) . optimise) firstSteps
  check "the circuit has multiple concrete first steps" (length targets > 1)
  mapM_
    ( \target -> do
        check "each branch reaches the green self-loop" (HG.isomorphic greenLoop target)
        checkMatrix target expected
    )
    targets

checkCombinedCleanup :: Property ()
checkCombinedCleanup = do
  checks <- either testFailed pure referenceCleanupRules
  templates <- either testFailed pure (symbolicPortOverlaps (map snd checks))
  let hasFusionAndParallelEdges (R.PortGraph ns boundary boxes) =
        case [IS.fromList [n | R.Node n <- os] | HG.Box (Spider Z _) [] os <- boxes] of
          [a, b] ->
            length ns == 5
              && null boundary
              && length boxes == 4
              && length [() | HG.Box Hadamard _ _ <- boxes] == 2
              && IS.size (IS.intersection a b) == 1
          _ -> False
  source <-
    maybe (testFailed "expected two spiders linked by a wire and two Hadamard edges") pure $
      find hasFusionAndParallelEdges templates
  joined <-
    either testFailed pure $
      Completion.checkPortTemplateWithScalars zxPortSymmetry symbolicScalar (Just 4) checks source
  case joined of
    Completion.PortTemplateJoinable _ -> pure ()
    _ -> testFailed "expected fusion and parallel cancellation to join up to scalar products"

overlapTests :: [TestTree]
overlapTests =
  [ testProperty "a symbolic variadic spider fusion fork joins" checkVariadicFusionFork
  , testProperty "a learned variadic rule preserves a symbolic sum of phases" checkPhaseCompletion
  , testProperty "ZX completion abstracts a shared phase sum to remove two Hadamard loops" checkHadamardLoopCompletion
  , testProperty
      "ZX completion learns all orders of parallel Hadamard cancellation between spiders"
      checkParallelHadamardCompletion
  , testProperty "the spider cleanup rules join on generated overlaps" checkSpiderCleanupOverlaps
  , testProperty "explicit interface wires cannot match opaque sequences" checkSequenceMarkers
  , testProperty "mixed parallel identities join with open and closed boundaries" checkMixedParallelIdentities
  , testProperty "combined fixed-topology ZX cleanup overlaps" checkCombinedCleanup
  , testProperty "colour change and fusion join with opaque legs" checkColourChangeFusion
  , testProperty "Hadamard chain cancellation joins up to leg order" checkHadamardChainSymmetry
  , testProperty "Hadamard chain cancellation joins red identity removal through colour change" checkHadamardChainIdentity
  , testProperty "scalar zero joins Hadamard loop and identity removal" checkHadamardLoopZero
  , testProperty
      "ZX completion learns the isolated Hadamard trace from one attached-loop equation"
      checkHadamardTraceCompletion
  , testProperty "five ZX seed equations cover all thirteen Hadamard variants" checkCombinedHadamardCompletion
  ]
