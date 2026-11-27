module Props.HypergraphRewrite.Completion (test) where

import Control.Monad (forM, forM_)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Monoid (Sum (..))
import Data.Type.Nat (Nat0, Nat1)
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.FinRel (FINREL (FR))
import Proarrow.Category.Instance.OpenHypergraph (W1, W2, W3)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Monoidal (MonoidalProfunctor ((**)), SymMonoidal (swap))
import Proarrow.Core (Promonad (id, (.)), type (~>))
import Proarrow.Monoid qualified as Mon
import Proarrow.Testing (check, expect)
import Proarrow.Tools.HypergraphRewrite ((==>))
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion

test :: TestTree
test =
  testGroup
    "Hypergraph completion"
    [ completionTests
    , pathContextTests
    , testProperty "confluence checks keep the overlap boundary when comparing reducts" checkHypergraphBoundary
    , localOption (mkTimeout 5000000) $
        testProperty "boundary identifications rule out isomorphism before searching" checkWideBoundaryMismatch
    , localOption (mkTimeout 5000000) $
        testProperty "box-only rewrites skip disjoint wide overlaps" checkWideDisjointOverlap
    , localOption (mkTimeout 5000000) $
        testProperty "graph comparison checks box shapes and sort multiplicities before searching" checkGraphMultiplicities
    , localOption (mkTimeout 5000000) $
        testProperty "disjoint deletion overlaps require a compatible node sort" checkDisjointSortedOverlap
    , localOption (mkTimeout 5000000) $
        testProperty "wire-only merges need two compatible nodes" checkDisjointSortedMerge
    , testProperty "hypergraph completion removes redundant rules and simplifies right sides" checkHypergraphInterreduction
    , testProperty "a nonjoinable port fork retains the shared sequence in its witness" checkPortTemplateWitness
    , testProperty "a variadic overlap gives a rule that joins the fork" checkPortOverlapOrientation
    , testProperty "completion rejects a rule that loops on empty captures" checkEmptyCaptureOrientation
    , testProperty "port completion finds a normal form on a shorter rewrite path" checkPortCompletionNormalForm
    , testProperty "a learned variadic rule creates a fork that needs a second rule" checkPortCompletionRounds
    , testProperty "exact port lists constrain symbolic overlap arities" checkPortOverlapArity
    , testProperty "shared numbered ports agree across both boxes" checkSharedPortNodes
    , testProperty "symmetric port comparison preserves boundary order and multiplicities" checkSymmetricPorts
    , localOption (mkTimeout 5000000) $
        testProperty "symmetric matching generates distinct repeated-port variants" checkRepeatedPortVariants
    , testProperty "scalar comparison preserves wired boxes and unequal products" checkScalarProducts
    , testProperty "symbolic port forks track interface identifications at the boundary" checkPortInterfaceMerge
    , testProperty "learned port rules can merge additional interface wires" checkLearnedInterfaceMerge
    , testProperty "generated port overlaps include shared interface wires outside shared boxes" checkPortInterfaceOverlap
    , testProperty "disjoint port matches overlap when one merges two wires needed by the other" checkPortWireOnlyOverlap
    , testProperty "wire-only overlaps include computed port replacements" checkComputedWireOnlyOverlap
    , localOption (mkTimeout 5000000) $
        testProperty "wire-only overlaps prune inapplicable computed replacements" checkComputedWireOnlyPruning
    , testProperty "generated port overlaps unify repeated label parameters and literals" checkPortParameterOverlap
    , testProperty "computed port replacements require known capture lengths" checkComputedPortReplacements
    , testProperty "computed overlaps specialise unshared captures to empty" checkUnsharedComputedCapture
    , testProperty "pointwise maps join only when both branches carry the same boundary map" checkSymbolicPortMaps
    , testProperty "pointwise map forks retain opaque captures and boundary maps" checkMappedFork
    ]

type Diagram l as bs = (HG.Wires as :: HG.OPENHG () l) ~> HG.Wires bs

type Wire l = HG.Wires @() @l W1

wire :: Wire l ~> Wire l
wire = id

checkPortTemplateWitness :: Property ()
checkPortTemplateWitness = do
  let template label = R.PortGraph [] [] [HG.Box label [R.Capture "legs"] []]
      source = template 's'
  left <- either testFailed pure (R.portRule source (template 'l'))
  right <- either testFailed pure (R.portRule source (template 'r'))
  overlaps <- either testFailed pure (Completion.portOverlapTemplates [left, right])
  overlap <- case overlaps of
    [fork] -> pure fork
    _ -> testFailed "expected one generated overlap on the shared box"
  result <- either testFailed pure (Completion.checkPortTemplate (Just 0) [(False, left), (True, right)] overlap)
  case result of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True host l r) ->
      forM_ [(host, 's'), (l, 'l'), (r, 'r')] \(g, label) -> do
        let (nodes, ins, outs, boxes) = HG.hypergraphParts g
        expect
          "the captured sequence stays at the boundary"
          (1, [0], [], [HG.Box label [0] []])
          (length nodes, ins, outs, boxes)
    _ -> testFailed "expected the two irreducible port replacements as a witness"

checkPortOverlapOrientation :: Property ()
checkPortOverlapOrientation = do
  let incoming = R.Capture "incoming"
      outgoing = R.Capture "outgoing"
      first = HG.Box 'a' [incoming] [R.Node 0]
      second = HG.Box 'b' [R.Node 0] [R.Node 1]
      third = HG.Box 'c' [R.Node 1, R.Node 2] [outgoing]
      oneWire = HG.sortList @() @W1
      twoWires = HG.sortList @() @W2
      threeWires = HG.sortList @() @W3
      contracted label = R.PortGraph oneWire [0] [HG.Box label [R.Node 0, incoming] [outgoing]]
      rank (R.PortGraph _ _ boxes) = (length boxes, length (filter ((== 't') . HG.label) boxes))
      order l r = compare (rank l) (rank r)
  prefix <-
    either testFailed pure $
      R.portRule (R.PortGraph twoWires [1] [first, second]) (R.PortGraph oneWire [0] [HG.Box 'd' [incoming] [R.Node 0]])
  whole <- either testFailed pure (R.portRule (R.PortGraph threeWires [2] [first, second, third]) (contracted 't'))
  candidates <- either testFailed pure (Completion.portOverlapTemplates [prefix, whole])
  source <- case candidates of
    [candidate] -> pure candidate
    _ -> testFailed "expected one overlap of prefix and whole-chain contraction"
  let seeds = [("prefix", prefix), ("whole", whole)]
  fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) seeds source)
  case fork of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap "prefix" "whole" _ _ _) -> pure ()
    _ -> testFailed "expected the two chain contractions to get stuck"
  derived <- either testFailed pure (Completion.orientPortOverlap order source fork)
  case Completion.orientPortOverlap (\_ _ -> EQ) source fork of
    Left _ -> pure ()
    Right _ -> testFailed "an ordering tie must not create a rule"
  let completed = seeds ++ [("suffix", derived)]
  overlaps <- either testFailed pure (Completion.portOverlapTemplates (map snd completed))
  forM_ (source : overlaps) \template -> do
    result <- either testFailed pure (Completion.checkPortTemplate (Just 1) completed template)
    case result of
      Completion.PortTemplateJoinable _ -> pure ()
      _ -> testFailed "expected the derived rule to close the forks"
  compiledSeeds <- either testFailed pure (R.compileReducingRules seeds)
  compiled <- either testFailed pure (R.compileReducingRules completed)
  finish <- either testFailed pure (R.portRule (contracted 't') (contracted 'u'))
  let initial = [prefix, whole, finish]
  ruleLimit <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 0 1 order) initial)
  case ruleLimit of
    Completion.PortIncomplete _ (Completion.PortRuleLimit _ (Completion.CriticalOverlap 0 1 _ _ _)) -> pure ()
    _ -> testFailed "expected the missing contraction at the rule limit"
  joinLimit <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 1 0 order) initial)
  case joinLimit of
    Completion.PortIncomplete _ (Completion.PortJoinLimit _ (Completion.CriticalOverlap 0 1 _ _ _)) -> pure ()
    _ -> testFailed "the fork needs more search depth once the finish rule is present"
  automatic <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 1 1 order) initial)
  automaticRules <- case automatic of
    Completion.PortComplete final ready -> do
      expect "completion adds one rule" 4 (length final)
      pure ready
    _ -> testFailed "completion should learn the missing contraction"
  forM_ [([], []), ([2], [3, 3]), ([2, 4, 2], [2, 3])] \(ins, outs) -> do
    let host :: Diagram Char W3 '[]
        host =
          HG.unsafeOpenHypergraph
            (twoWires ++ threeWires)
            [2, 3, 4]
            []
            [HG.Box 'a' ins [0], HG.Box 'b' [0] [1], HG.Box 'c' [1, 4] outs]
    case R.rewritesCompiled compiledSeeds host of
      [("prefix", l), ("whole", r)] -> do
        let normalised = R.normalise R.unlimitedRewrites compiled l
        expect "the derived rule reduces the residual chain in one step" 1 (R.normalisationRewrites normalised)
        check "the two concrete reductions agree" (HG.isomorphic (R.normalisedGraph normalised) r)
        case (R.rewritesCompiled automaticRules l, R.rewritesCompiled automaticRules r) of
          ([(3, joinedLeft)], [(2, joinedRight)]) ->
            check "completion learns a direct rule to the simplified branch" (HG.isomorphic joinedLeft joinedRight)
          _ -> testFailed "expected one further step from each concrete branch"
      _ -> testFailed "expected one match for each seed rule"

checkEmptyCaptureOrientation :: Property ()
checkEmptyCaptureOrientation = do
  let fragment l ins = R.PortGraph [] [] [HG.Box l ins []]
      legs = [R.Capture "legs"]
      start = fragment 'a' legs
      withLegs = fragment 'b' legs
      withoutLegs = fragment 'b' []
      rank (R.PortGraph _ _ boxes) = (length [() | HG.Box 'a' _ _ <- boxes], sum (map (length . HG.inputs) boxes))
      order l r = compare (rank l) (rank r)
  preserve <- either testFailed pure (R.portRule start withLegs)
  erase <- either testFailed pure (R.portRule start withoutLegs)
  let seeds = [preserve, erase]
  result <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 1 1 order) seeds)
  case result of
    Completion.PortIncomplete rules (Completion.PortUnorientable _ source fork) -> do
      expect "only the seeds are retained" 2 (length rules)
      case Completion.orientPortOverlap order source (Completion.PortTemplateUnjoinable fork) of
        Left _ -> pure ()
        Right _ -> testFailed "orienting the fork directly must also reject the looping rule"
    _ -> testFailed "expected the learned rule to be rejected because B() would rewrite to itself"

checkPortCompletionNormalForm :: Property ()
checkPortCompletionNormalForm = do
  let fragment l = R.PortGraph [] [] [HG.Box l [] []]
      rank (R.PortGraph _ _ boxes) = sum [fromEnum 'e' - fromEnum (HG.label box) | box <- boxes]
      order l r = compare (rank l) (rank r)
  seeds <-
    either testFailed pure $
      traverse (\(l, r) -> R.portRule (fragment l) (fragment r)) [('a', 'c'), ('a', 'b'), ('c', 'd'), ('c', 'e'), ('d', 'e')]
  result <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 1 1 order) seeds)
  case result of
    Completion.PortComplete rules compiled -> do
      expect "completion learns one rule" 6 (length rules)
      case R.rewritesCompiled compiled (HG.box @Char @'[] @'[] 'b') of
        [(5, normal)] -> check "the learned rule reaches e directly" (HG.isomorphic (HG.box @Char @'[] @'[] 'e') normal)
        _ -> testFailed "expected the learned rule to rewrite b"
    _ -> testFailed "expected completion to reach e from c within one step"

checkPortCompletionRounds :: Property ()
checkPortCompletionRounds = do
  let incoming = R.Capture "incoming"
      outgoing = R.Capture "outgoing"
      oneWire = HG.sortList @() @W1
      twoWires = HG.sortList @() @W2
      a = R.Node 0
      b = R.Node 1
      first label = HG.Box label [incoming] [a]
      middle label = HG.Box label [a] [b]
      lastBox wire' label = HG.Box label [wire'] [outgoing]
      openPair l r target =
        R.portRule (R.PortGraph twoWires [1] [first l, middle r]) (R.PortGraph oneWire [0] [first target])
      joined label = R.PortGraph [] [] [HG.Box label [incoming] [outgoing]]
      boxCount (R.PortGraph _ _ boxes) = length boxes
      order l r = compare (boxCount l) (boxCount r)
  seeds <-
    either testFailed pure $
      sequence
        [ openPair 'a' 'b' 'd'
        , R.portRule (R.PortGraph twoWires [] [first 'a', middle 'b', lastBox b 'c']) (joined 't')
        , openPair 'x' 'd' 'y'
        , R.portRule (R.PortGraph oneWire [] [first 'x', lastBox a 't']) (joined 'v')
        ]
  initial <- either testFailed pure (Completion.portOverlapTemplates seeds)
  expect "the seeds only overlap on the original chain" 1 (length initial)
  oneRound <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 1 2 order) seeds)
  case oneRound of
    Completion.PortIncomplete rules (Completion.PortRuleLimit _ (Completion.CriticalOverlap 2 4 host left right)) -> do
      expect "one learned rule is retained" 5 (length rules)
      let labels diagram = let (_, _, _, boxes) = HG.hypergraphParts diagram in sort (map HG.label boxes)
      expect "the learned rule overlaps on the extended chain" "cdx" (labels host)
      expect "the new fork contracts either the prefix or the suffix" ["cy", "tx"] (sort [labels left, labels right])
    _ -> testFailed "expected the new fork to involve seed rule 2 and learned rule 4"
  twoRounds <- either testFailed pure (Completion.completePorts (Completion.PortCompletionOptions 2 2 order) seeds)
  compiled <- case twoRounds of
    Completion.PortComplete rules ready -> do
      expect "completion learns a second rule" 6 (length rules)
      pure ready
    _ -> testFailed "expected completion to close both forks"
  let source :: Diagram Char W2 '[]
      source =
        HG.unsafeOpenHypergraph
          (HG.sortList @() @W3 ++ twoWires)
          [3, 4]
          []
          [HG.Box 'x' [3, 4, 3] [0], HG.Box 'a' [0] [1], HG.Box 'b' [1] [2], HG.Box 'c' [2] [4, 4]]
  (firstBranch, otherBranch) <- case R.rewritesCompiled compiled source of
    [(0, l), (1, r)] -> pure (l, r)
    _ -> testFailed "expected the original fork inside the extended concrete chain"
  residual <-
    maybe
      (testFailed "expected prefix contraction after the first seed rule")
      pure
      (lookup 2 (R.rewritesCompiled compiled firstBranch))
  final <- case R.rewritesCompiled compiled residual of
    [(5, target)] -> pure target
    _ -> testFailed "expected only the second learned rule on the residual chain"
  let expected = HG.unsafeOpenHypergraph @_ @W2 @'[] twoWires [0, 1] [] [HG.Box 'v' [0, 1, 0] [1, 1]]
      other = R.normalisedGraph (R.normalise R.unlimitedRewrites compiled otherBranch)
  check "the learned rule preserves the repeated captured ports" (HG.isomorphic final expected)
  check "both branches of the extended chain agree" (HG.isomorphic final other)

checkSymmetricPorts :: Property ()
checkSymmetricPorts = do
  let a = R.Capture "a"
      b = R.Capture "b"
      source = R.PortGraph [] [] [HG.Box 's' [a] [b]]
      target ports = R.PortGraph [] [] [HG.Box 't' ports []]
      symmetry _ = Completion.SymmetricInputs
      comparePorts leftPorts rightPorts = do
        left <- either testFailed pure (R.portRule source (target leftPorts))
        right <- either testFailed pure (R.portRule source (target rightPorts))
        either testFailed pure $
          Completion.checkPortTemplateWithSymmetry symmetry (Just 0) [(False, left), (True, right)] source
      expectDistinct message leftPorts rightPorts = do
        result <- comparePorts leftPorts rightPorts
        case result of
          Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> pure ()
          _ -> testFailed message
  permuted <- comparePorts [a, b] [b, a]
  case permuted of
    Completion.PortTemplateJoinable count -> expect "one fork joins by permuting its inputs" 1 count
    _ -> testFailed "expected a permutation of symmetric inputs to join"
  expectDistinct "expected different boundary ports to stay distinct" [a] [b]
  expectDistinct "expected different multiplicities to stay distinct" [a, a, b] [a, b, b]

checkRepeatedPortVariants :: Property ()
checkRepeatedPortVariants = do
  let sorts = HG.sortList @() @W2
      a = R.Node 0
      b = R.Node 1
      outputs = [b, a]
      fragment label ins = R.PortGraph sorts [0, 1] [HG.Box (Other (R.Literal (label :: Int))) ins outputs]
      checkVariants original wanted = do
        rule <- either testFailed pure (R.parameterPortRule (fragment 0 original) (fragment 1 original))
        variants <- either testFailed pure (R.parameterPortVariants (const R.SymmetricInputs) rule)
        examples <- either testFailed pure (traverse (R.parameterPortExample (const 0)) variants)
        actual <- forM examples \case
          (R.PortGraph _ [0, 1] [HG.Box (Other 0) ins outs], R.PortGraph _ [0, 1] [rhs]) -> do
            expect "outputs stay ordered" outputs outs
            expect "the replacement stays ordered" (HG.Box (Other 1) original outputs) rhs
            pure ins
          _ -> testFailed "expected the same boundary and labels in every variant"
        expect "the original rule has first priority" [original] (take 1 actual)
        expect "each distinct input order occurs once" (sort wanted) (sort actual)
  let repeated = replicate 12 a
  checkVariants repeated [repeated]
  checkVariants [a, b, a] [[a, b, a], [a, a, b], [b, a, a]]

checkScalarProducts :: Property ()
checkScalarProducts = do
  let leg = R.Capture "leg"
      source = R.PortGraph [] [] [HG.Box 's' [leg] []]
      factors = [HG.Box 'p' [] [], HG.Box 'm' [] []]
      scalar 'p' = Just (Sum (1 :: Int))
      scalar 'm' = Just (Sum (-1))
      scalar _ = Nothing
      compareWithEmpty boxes = do
        left <- either testFailed pure (R.portRule source (R.PortGraph [] [] boxes))
        right <- either testFailed pure (R.portRule source (R.PortGraph [] [] []))
        either testFailed pure $
          Completion.checkPortTemplateWithScalars
            (const Completion.OrderedPorts)
            scalar
            (Just 0)
            [(False, left), (True, right)]
            source
      expectDistinct boxes = do
        result <- compareWithEmpty boxes
        case result of
          Completion.PortTemplateUnjoinable _ -> pure ()
          _ -> testFailed "expected a scalar or wiring difference to distinguish the branches"
  joined <- compareWithEmpty factors
  case joined of
    Completion.PortTemplateJoinable count -> expect "inverse factors cancel" 1 count
    _ -> testFailed "expected equal scalar products to join"
  expectDistinct [HG.Box 'p' [] []]
  expectDistinct (HG.Box 'p' [leg] [] : factors)

checkPortInterfaceMerge :: Property ()
checkPortInterfaceMerge = do
  let sorts = HG.sortList @() @W2
      source = R.PortGraph sorts [0, 1] [HG.Box 's' [R.Node 0, R.Node 1] []]
  merge <- either testFailed pure (R.portRule source (R.PortGraph (HG.sortList @() @W1) [0, 0] []))
  keep <- either testFailed pure (R.portRule source (R.PortGraph sorts [0, 1] []))
  templates <- either testFailed pure (Completion.portOverlapTemplates [merge, keep])
  overlap <- case [template | template@(R.PortGraph _ _ [_]) <- templates] of
    [template] -> pure template
    _ -> testFailed "expected one generated overlap with both interface wires"
  result <-
    either testFailed pure $
      Completion.checkPortTemplateWithSymmetry
        (const Completion.SymmetricPorts)
        (Just 0)
        [(False, merge), (True, keep)]
        overlap
  case result of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ left right) -> do
      let (_, merged, _, _) = HG.hypergraphParts left
          (_, distinct, _, _) = HG.hypergraphParts right
      expect "the merged wire still occupies both boundary positions" [0, 0] merged
      expect "the other rule keeps both wires distinct" [0, 1] distinct
    _ -> testFailed "expected boundary identification to distinguish the branches"
  withFresh <- either testFailed pure (R.portRule source (R.PortGraph sorts [0, 0] []))
  freshResult <-
    either testFailed pure $
      Completion.checkPortTemplate (Just 0) [(False, merge), (True, withFresh)] overlap
  case freshResult of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ right) -> do
      let (nodes, boundary, _, _) = HG.hypergraphParts right
      expect "the replacement adds an isolated node alongside the merged wire" (2, [0, 0]) (length nodes, boundary)
    _ -> testFailed "expected the fresh node to distinguish the branches"

checkLearnedInterfaceMerge :: Property ()
checkLearnedInterfaceMerge = do
  let fragment sorts boundary l ins = R.PortGraph sorts boundary [HG.Box l (map R.Node ins) []]
      source = fragment (HG.sortList @() @W3) [0, 1, 2] 's' [0, 1, 2]
      left = fragment (HG.sortList @() @W2) [0, 0, 1] 'l' [0, 1]
      right = fragment (HG.sortList @() @W1) [0, 0, 0] 'r' [0]
      rank (R.PortGraph ns _ _) = length ns
      order l r = compare (rank l) (rank r)
  mergeTwo <- either testFailed pure (R.portRule source left)
  mergeAll <- either testFailed pure (R.portRule source right)
  let seeds = [("merge two", mergeTwo), ("merge all", mergeAll)]
  fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) seeds source)
  learned <- either testFailed pure (Completion.orientPortOverlap order source fork)
  case fork of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap _ _ _ l r) ->
      case R.rewrites learned l of
        [target] -> check "the learned rule reaches the fully merged branch" (HG.isomorphic target r)
        _ -> testFailed "expected one match after the first merge"
    _ -> testFailed "expected the two seed merges to disagree"
  case Completion.orientPortOverlap (flip order) source fork of
    Left _ -> pure ()
    Right _ -> testFailed "orientation must reject splitting a merged wire"

checkPortInterfaceOverlap :: Property ()
checkPortInterfaceOverlap = do
  let sorts = HG.sortList @() @W1
      empty = R.PortGraph [] [] []
      keep = R.PortGraph sorts [0] []
      wireBox name = HG.Box name [R.Node 0] []
      marker = HG.Box 's' [] []
      source name = R.PortGraph sorts [0] [marker, wireBox name]
  left <- either testFailed pure (R.portRule (source 'l') keep)
  right <- either testFailed pure (R.portRule (source 'r') keep)
  templates <- either testFailed pure (Completion.portOverlapTemplates [left, right])
  let boundaries =
        [ length boundary
        | R.PortGraph _ boundary boxes <- templates
        , sort (map HG.label boxes) == "lrs"
        ]
  expect "preserved ports can be identified away from the shared box" [1, 2] (sort boundaries)
  preserve <- either testFailed pure (R.portRule (R.PortGraph sorts [0] [wireBox 's']) keep)
  delete <- either testFailed pure (R.portRule (R.PortGraph sorts [] [wireBox 's', wireBox 't']) empty)
  withAttachment <- either testFailed pure (Completion.portOverlapTemplates [preserve, delete])
  case withAttachment of
    [R.PortGraph nodes boundary boxes] -> do
      expect "the shared wire reaches both boxes" (1, [wireBox 's', wireBox 't']) (length nodes, boxes)
      expect "a wire deleted by either match is internal" [] boundary
    _ -> testFailed "expected one overlap with an attachment allowed by the preserving match"

checkPortWireOnlyOverlap :: Property ()
checkPortWireOnlyOverlap = do
  let sorts = HG.sortList @() @W2
      source = R.PortGraph (HG.sortList @() @HG.W3) [0, 1, 2] [HG.Box 'l' (map R.Node [0, 1, 2]) []]
      other = R.PortGraph sorts [0, 1] [HG.Box 'r' (map R.Node [0, 1]) []]
  merge <- either testFailed pure (R.portRule source (R.PortGraph sorts [0, 0, 1] []))
  preserve <- either testFailed pure (R.portRule other (R.PortGraph sorts [0, 1] []))
  templates <- either testFailed pure (Completion.portOverlapTemplates [merge, preserve])
  let mixed = [(template, ports) | template@(R.PortGraph _ _ [HG.Box 'l' _ _, HG.Box 'r' ports _]) <- templates]
  expect "only the two orders of the merged pair overlap" [map R.Node [0, 1], map R.Node [1, 0]] (sort (map snd mixed))
  forM_ mixed \(template, _) -> do
    result <- either testFailed pure (Completion.checkPortTemplate (Just 1) [(False, merge), (True, preserve)] template)
    case result of
      Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> pure ()
      _ -> testFailed "expected the merge to block the other match by identifying its wires"

data ParameterLabel a = Shared a a | Other a
  deriving (Eq, Show, Functor, Foldable, Traversable)

checkComputedWireOnlyOverlap :: Property ()
checkComputedWireOnlyOverlap = do
  let sorts = HG.sortList @() @W2
      tagged l extra = R.PortGraph sorts [0, 1] [HG.Box (fmap R.Literal l) ([R.Node 0, R.Node 1] ++ extra) []]
      marker = tagged (Shared (0 :: Int) 0)
      keep = R.PortGraph sorts [0, 1] []
      merge = R.PortGraph (HG.sortList @() @W1) [0, 0] []
      before = tagged (Other 0)
      after = tagged (Other 1) []
      legs = [R.Capture "legs"]
      fresh = (+ 100)
      checkFork rules = do
        result <-
          either testFailed (pure . fst) $
            Completion.completeParameterPorts
              (Completion.parameterPortOptions fresh R.Literal R.Literal)
              (Completion.PortCompletionOptions 0 1 (\_ _ -> EQ))
              rules
        case result of
          Completion.PortIncomplete _ (Completion.PortRuleLimit _ (Completion.CriticalOverlap 0 1 _ left right)) -> do
            let shape graph =
                  let (_, boundary, _, boxes) = HG.hypergraphParts graph in (boundary, map HG.label boxes)
            pure (shape left, shape right)
          _ -> testFailed "expected a fork between the wire merge and the disjoint relabeling"
  fixedMerge <- either testFailed pure (R.parameterPortRule (marker []) merge)
  fixedRelabel <- either testFailed pure (R.parameterPortRule (before []) after)
  computedMerge <- either testFailed pure (R.parameterPortRuleWith (marker []) (const merge))
  computedRelabel <- either testFailed pure (R.parameterPortRuleWith (before []) (const after))
  mergeAtZero <-
    either testFailed pure $
      R.parameterPortRuleWith (marker legs) \sizes -> if sizes Map.! "legs" == 0 then merge else keep
  variadicRelabel <- either testFailed pure (R.parameterPortRuleWith (before legs) (const after))
  expected <- checkFork [fixedMerge, fixedRelabel]
  forM_
    [ [fixedMerge, computedRelabel]
    , [computedMerge, fixedRelabel]
    , [computedMerge, computedRelabel]
    , [mergeAtZero, fixedRelabel]
    , [fixedMerge, variadicRelabel]
    , [mergeAtZero, variadicRelabel]
    ]
    \rules -> do
      actual <- checkFork rules
      expect "fixed and computed replacements witness the same fork" expected actual
  computedKeep <- either testFailed pure (R.parameterPortRuleWith (marker []) (const keep))
  independent <- either testFailed pure (Completion.parameterPortOverlapTemplates fresh [computedKeep, computedRelabel])
  expect "disjoint matches with no wire merge produce no templates" 0 (length independent)

checkComputedWireOnlyPruning :: Property ()
checkComputedWireOnlyPruning = do
  let sorts = concat (replicate 10 (HG.sortList @() @W1))
      boundary = [0 .. length sorts - 1]
      label = Other (R.Literal (0 :: Int))
      exact l = R.PortGraph sorts boundary [HG.Box l (map R.Node boundary) []]
      variadic = R.PortGraph sorts boundary [HG.Box label (map R.Node boundary ++ [R.Capture "legs"]) []]
      merged = R.PortGraph (HG.sortList @() @W1) (map (const 0) boundary)
      noTemplates reason lhs build = do
        computed <- either testFailed pure (R.parameterPortRuleWith lhs build)
        templates <- either testFailed pure (Completion.parameterPortOverlapTemplates (+ 100) [computed])
        expect reason 0 (length templates)
  noTemplates "the zero-length replacement must merge wires to create a candidate" variadic \sizes ->
    if sizes Map.! "legs" == 0 then exact label else merged []
  noTemplates "an indexed port cannot match an empty capture" variadic $
    const (merged [HG.Box label [R.Element "legs" 0] []])
  noTemplates "wire-only relabeling cannot create a fork" (exact label) (const (exact (Other (R.Literal 1))))

checkComputedPortReplacements :: Property ()
checkComputedPortReplacements = do
  let legs = R.Capture "legs"
      value = R.Variable "value"
      fragment label ports = R.PortGraph [] [] [HG.Box label ports []]
      patternGraph = fragment (Shared value value) [legs]
      source ns boundary ports = R.PortGraph ns boundary [HG.Box (Shared (7 :: Int) 7) ports []]
      oneWire = HG.sortList @() @W1
  fixed <- either testFailed pure (R.parameterPortRule patternGraph (fragment (Other value) [legs]))
  computed <- either testFailed pure $
    R.parameterPortRuleWith patternGraph \sizes ->
      fragment (Other value) [R.Element "legs" i | i <- [0 .. sizes Map.! "legs" - 1]]
  let checkFork template wanted = do
        result <- either testFailed pure (Completion.checkPortTemplate (Just 0) [(False, fixed), (True, computed)] template)
        case result of
          Completion.PortTemplateJoinable count -> expect "number of applicable forks" wanted count
          _ -> testFailed "expected the applicable rules to reach the same diagram"
  checkFork (source [] [] []) 1
  checkFork (source oneWire [0] [R.Node 0, R.Node 0]) 1
  let R.PortGraph ns boundary boxes = source oneWire [0] [R.Node 0]
  checkFork (R.PortGraph ns boundary (HG.Box (Other 8) [legs] [] : boxes)) 1
  checkFork (source [] [] [legs]) 0
  checkFork (source oneWire [0] [R.Node 0, legs]) 0
  let exact label = R.PortGraph oneWire [0] [HG.Box label [R.Node 0, R.Node 0] []]
      fresh = (+ 100)
  fixedExact <- either testFailed pure (R.parameterPortRule (exact (Shared (R.Literal 7) value)) (exact (Other value)))
  overlaps <- either testFailed pure (Completion.parameterPortOverlapTemplates fresh [fixedExact, computed])
  case overlaps of
    [R.PortGraph _ [0] [box]] ->
      expect "the exact rule fixes the capture length and labels" (HG.Box (Shared 7 7) [R.Node 0, R.Node 0] []) box
    _ -> testFailed "expected only the overlap with an exact port list"
  different <- either testFailed pure (R.parameterPortRule patternGraph (fragment (Other (R.Literal 8)) [legs]))
  nullary <- either testFailed pure (Completion.parameterPortOverlapTemplates fresh [different, computed])
  case nullary of
    [template@(R.PortGraph [] [] [HG.Box (Shared _ _) [] []])] -> do
      fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) [(False, different), (True, computed)] template)
      case fork of
        Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> pure ()
        _ -> testFailed "expected the two nullary replacements to disagree"
    _ -> testFailed "expected the overlap at arity zero"
  missingPort <-
    either testFailed pure (R.parameterPortRuleWith patternGraph (const (fragment (Other value) [R.Element "legs" 2])))
  rejected <- either testFailed pure (Completion.parameterPortOverlapTemplates fresh [fixedExact, missingPort])
  expect "the computed replacement must be valid at the matched length" 0 (length rejected)

checkUnsharedComputedCapture :: Property ()
checkUnsharedComputedCapture = do
  let oneWire = HG.sortList @() @W1
      fragment = R.PortGraph oneWire [0]
      link = R.Node 0
      a = HG.Box (Shared (0 :: Int) 0) [link] []
      b = HG.Box (Other 1) [] [link]
      c = HG.Box (Shared 2 2) [link] []
      literals = fragment . map (\(HG.Box l ins outs) -> HG.Box (fmap R.Literal l) ins outs)
  fixed <- either testFailed pure (R.parameterPortRule (literals [a]) (literals [c]))
  computed <-
    either testFailed pure $
      R.parameterPortRuleWith (literals [a, b{HG.outputs = [link, R.Capture "legs"]}]) \sizes ->
        literals [HG.Box (Other 3) [] (link : [R.Element "legs" i | i <- [0 .. sizes Map.! "legs" - 1]])]
  forM_ [[fixed, computed], [computed, fixed]] \rules -> do
    templates <- either testFailed pure (Completion.parameterPortOverlapTemplates (+ 100) rules)
    case [template | template@(R.PortGraph _ [0] boxes) <- templates, boxes == [a, b]] of
      [template] -> do
        fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) (zip [False, True] rules) template)
        case fork of
          Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> pure ()
          _ -> testFailed "expected the fixed and computed rules to disagree at arity zero"
      _ -> testFailed "expected an overlap with an empty capture on the unshared box"

checkSymbolicPortMaps :: Property ()
checkSymbolicPortMaps = do
  let box value = HG.Box (Other (value :: Int)) [] [R.Capture "legs"]
      diagram = R.PortGraph [] []
      patternGraph = diagram . pure . relabel
      relabel (HG.Box l ins outs) = HG.Box (fmap R.Literal l) ins outs
      pointwise side mapping ends =
        R.parameterPortRuleMap
          (patternGraph (box side))
          [("legs", HG.Box (Other (R.Literal mapping)) [] ends)]
          (patternGraph (box 3))
  left <- either testFailed pure (R.parameterPortRule (patternGraph (box 0)) (patternGraph (box 1)))
  right <- either testFailed pure (R.parameterPortRule (patternGraph (box 0)) (patternGraph (box 2)))
  let ends = [R.Outer, R.Inner]
  mapLeft <- either testFailed pure (pointwise 1 4 ends)
  mapRight <- either testFailed pure (pointwise 2 4 ends)
  mapReversed <- either testFailed pure (pointwise 1 4 (reverse ends))
  mapDifferent <- either testFailed pure (pointwise 2 5 ends)
  let source = diagram [box 0]
      checkFork template rules =
        either testFailed pure (Completion.checkPortTemplate (Just 1) (zip [0 :: Int ..] (left : right : rules)) template)
      expectUnjoinable message = \case
        Completion.PortTemplateUnjoinable (Completion.CriticalOverlap 0 1 _ _ _) -> pure ()
        _ -> testFailed message
  checkFork source [mapLeft, mapRight] >>= \case
    Completion.PortTemplateJoinable 1 -> pure ()
    _ -> testFailed "expected both branches to attach the same map to the opaque sequence"
  checkFork source [mapLeft, mapDifferent] >>= expectUnjoinable "different boundary maps cannot witness the join"
  let mappedSource = diagram [box 1]
      mappedRules = [(False, mapLeft), (True, mapReversed)]
      symmetry l
        | l == Other 4 = Completion.SymmetricOutputs
        | otherwise = Completion.OrderedPorts
  exact <- either testFailed pure (Completion.checkPortTemplate (Just 0) mappedRules mappedSource)
  case exact of
    Completion.PortTemplateMappedUnjoinable{} -> pure ()
    _ -> testFailed "expected ordered boundary maps to retain their endpoint positions"
  symmetric <-
    either testFailed pure (Completion.checkPortTemplateWithSymmetry symmetry (Just 0) mappedRules mappedSource)
  case symmetric of
    Completion.PortTemplateJoinable 1 -> pure ()
    _ -> testFailed "expected the reversed outputs of a symmetric boundary box to join"
  checkFork (diagram [box 0, box 6]) [mapLeft, mapRight]
    >>= expectUnjoinable "a shared marker cannot carry an occurrence-local map"

checkMappedFork :: Property ()
checkMappedFork = do
  let fragment n = R.PortGraph [] [] [HG.Box (Other (R.Literal (n :: Int))) [] [R.Capture "legs"]]
      decorate n target =
        R.parameterPortRuleMap (fragment n) [("legs", HG.Box (Other (R.Literal 4)) [] [R.Outer, R.Inner])] (fragment target)
      fresh = (+ 100)
      rank (R.PortGraph _ _ boxes) = sum [3 - min 3 n | HG.Box (Other n) _ _ <- boxes]
      order l r = compare (rank l) (rank r)
  relabel <- either testFailed pure (R.parameterPortRule (fragment 0) (fragment 1))
  direct <- either testFailed pure (decorate 0 2)
  later <- either testFailed pure (decorate 1 2)
  templates <- either testFailed pure (Completion.parameterPortOverlapTemplates fresh [relabel, direct])
  case templates of
    [template@(R.PortGraph [] [] [HG.Box (Other 0) [] [R.Capture name]])] -> do
      let checkWith depth rs = either testFailed pure (Completion.checkPortTemplate (Just depth) (zip [0 :: Int ..] rs) template)
          complete budget rs =
            either testFailed (pure . fst) $
              Completion.completeParameterPorts
                (Completion.parameterPortOptions fresh R.Literal R.Literal)
                (Completion.PortCompletionOptions budget 1 order)
                rs
          expectedMaps = [(name, [HG.Box (Other 4) [] [R.Outer, R.Inner]])]
      joined <- checkWith 1 [relabel, direct, later]
      case joined of
        Completion.PortTemplateJoinable count -> expect "one fork starts with a map on the opaque leg sequence" 1 count
        _ -> testFailed "expected the two maps to reach the same boundary"
      limited <- checkWith 0 [relabel, direct, later]
      case limited of
        Completion.PortTemplateMappedJoinLimit{} -> pure ()
        _ -> testFailed "expected a mapped fork to reach the depth bound"
      stuck <- checkWith 1 [relabel, direct]
      case stuck of
        Completion.PortTemplateMappedUnjoinable (Completion.MappedPortFork (Completion.CriticalOverlap 0 1 _ _ _) [] maps) -> do
          expect "the witness retains the map by capture name" expectedMaps maps
        _ -> testFailed "expected a failed join with a symbolic boundary map"
      case Completion.orientParameterPortOverlap R.Literal order template stuck of
        Left _ -> pure ()
        Right _ -> testFailed "a mapped fork cannot be reified as a plain port rule"
      exhausted <- complete 0 [relabel, direct]
      case exhausted of
        Completion.PortIncomplete retained (Completion.PortMappedRuleLimit _ witness) -> do
          expect "the rule budget preserves the seed rules" 2 (length retained)
          case witness of
            Completion.MappedPortFork (Completion.CriticalOverlap 0 1 _ _ _) [] maps ->
              expect "the rule limit retains the mapped fork" expectedMaps maps
            _ -> testFailed "expected the original mapped fork"
        _ -> testFailed "expected mapped rule-budget exhaustion before trying to orient the fork"
      completion <- complete 1 [relabel, direct]
      case completion of
        Completion.PortIncomplete _ Completion.PortMappedUnorientable{} -> pure ()
        _ -> testFailed "completion must preserve the mapped fork in its stop reason"
      different <- either testFailed pure (decorate 1 3)
      common <- complete 1 [relabel, direct, different]
      case common of
        Completion.PortIncomplete _ Completion.PortMappedUnorientable{} -> pure ()
        _ -> testFailed "completion must prove a left inverse before cancelling a common map"
    _ -> testFailed "expected one overlap with a symbolic sequence in the shared gap"

checkPortParameterOverlap :: Property ()
checkPortParameterOverlap = do
  let x = R.Variable "x"
      diagram labels = R.PortGraph [] [] [HG.Box l [] [] | l <- labels]
      fixed a b = R.parameterPortRule (diagram [Shared (R.Literal a) (R.Literal b)]) (diagram [])
      overlaps left right = do
        sources <- either testFailed pure (Completion.parameterPortOverlapTemplates (+ 100) [left, right])
        pure [map HG.label boxes | R.PortGraph [] [] boxes@[_, _] <- sources]
  repeated <- either testFailed pure (R.parameterPortRule (diagram [Shared x x, Other x]) (diagram []))
  agreeing <- either testFailed pure (fixed 7 7)
  disagreeing <- either testFailed pure (fixed 7 8)
  consistent <- overlaps repeated agreeing
  expect "the literal reaches the unshared occurrence" [[Shared 7 7, Other 7]] consistent
  conflicting <- overlaps repeated disagreeing
  expect "two different literals cannot bind the same variable" [] conflicting

checkPortOverlapArity :: Property ()
checkPortOverlapArity = do
  let tag ports = R.PortGraph [] [] [HG.Box 's' ports []]
      empty = R.PortGraph [] [] []
      link = R.Node 0
      pair = [HG.Box 's' [link] [], HG.Box 't' [] [link]]
  exact <- either testFailed pure (R.portRule (R.PortGraph (HG.sortList @() @W1) [] pair) empty)
  variadic <- either testFailed pure (R.portRule (tag [R.Capture "legs"]) empty)
  nullary <- either testFailed pure (R.portRule (tag []) empty)
  compatible <- either testFailed pure (Completion.portOverlapTemplates [exact, variadic])
  case compatible of
    [R.PortGraph nodes [] boxes] -> do
      expect "the overlap has just the numbered link" 1 (length nodes)
      expect "the shared port list is exact" pair boxes
    _ -> testFailed "expected one overlap with the sequence specialised to the exact port"
  incompatible <- either testFailed pure (Completion.portOverlapTemplates [exact, nullary])
  expect "incompatible exact lengths" 0 (length incompatible)
  let connected sorts label links =
        R.PortGraph
          sorts
          []
          [HG.Box 's' (R.Capture "before" : links ++ [R.Capture "after"]) [], HG.Box label [] links]
  adjacent <- either testFailed pure (R.portRule (connected (HG.sortList @() @W2) 'l' [R.Node 0, R.Node 1]) empty)
  single <- either testFailed pure (R.portRule (connected (HG.sortList @() @W1) 'r' [R.Node 0]) empty)
  interleaved <- either testFailed pure (Completion.portOverlapTemplates [adjacent, single])
  let orders =
        [ [i | R.Node i <- ports]
        | R.PortGraph _ _ boxes <- interleaved
        , 'l' `elem` map HG.label boxes
        , 'r' `elem` map HG.label boxes
        , HG.Box 's' ports [] <- boxes
        ]
  expect "the other link cannot split two adjacent numbered ports" [[0, 1, 2], [2, 0, 1]] (sort orders)

checkSharedPortNodes :: Property ()
checkSharedPortNodes = do
  let links = [R.Node 0, R.Node 1]
      sorts = HG.sortList @() @W2
      source other = R.PortGraph sorts [] [HG.Box 's' links [], HG.Box 't' [] other]
      target name = R.PortGraph [] [] [HG.Box name [] []]
  left <- either testFailed pure (R.portRule (source links) (target 'l'))
  right <- either testFailed pure (R.portRule (source links) (target 'r'))
  crossed <- either testFailed pure (R.portRule (source (reverse links)) (target 'r'))
  aligned <- either testFailed pure (Completion.portOverlapTemplates [left, right])
  case aligned of
    [overlap@(R.PortGraph nodes [] boxes)] -> do
      expect "each shared numbered node occurs once in the overlap" 2 (length nodes)
      expect "both boxes refer to the same ordered links" [HG.Box 's' links [], HG.Box 't' [] links] boxes
      result <- either testFailed pure (Completion.checkPortTemplate (Just 0) [(False, left), (True, right)] overlap)
      case result of
        Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> pure ()
        _ -> testFailed "expected both rules to match the shared boxes"
    _ -> testFailed "expected one overlap sharing both boxes and both nodes"
  incompatible <- either testFailed pure (Completion.portOverlapTemplates [left, crossed])
  expect "inconsistent identifications cannot be glued" 0 (length incompatible)
  let R.PortGraph _ _ boxes = source links
      attached = R.PortGraph sorts [] (boxes ++ [HG.Box 'u' [R.Node 0] []])
  withAttachment <- either testFailed pure (R.portRule attached (target 'r'))
  dangling <- either testFailed pure (Completion.portOverlapTemplates [left, withAttachment])
  expect "a shared node cannot touch an unshared box" 0 (length dangling)

checkHypergraphBoundary :: Property ()
checkHypergraphBoundary = do
  let marker = HG.box @String @W2 @'[] "marker"
      tag = HG.box @String @W1 @'[] "tag"
      discard = Mon.counit @(Wire String)
  left <- either testFailed pure (marker ==> tag ** discard)
  right <- either testFailed pure (marker ==> discard ** tag)
  result <- either testFailed pure (Completion.checkHypergraphConfluence Nothing [("left", left), ("right", right)])
  case result of
    Completion.HypergraphNotLocallyConfluent (Completion.CriticalOverlap "left" "right" _ l r) -> do
      let withoutBoundary g =
            let (nodes, _, _, boxes) = HG.hypergraphParts g
            in HG.unsafeOpenHypergraph @String @'[] @'[] nodes [] [] boxes
      check "the closed reducts are isomorphic" (HG.isomorphic (withoutBoundary l) (withoutBoundary r))
      check "the tag attaches to different boundary ports" (not (HG.isomorphic l r))
    _ -> testFailed "expected an unjoinable fork with an ordered boundary"

checkWideBoundaryMismatch :: Property ()
checkWideBoundaryMismatch = do
  let sorts = concat (replicate 12 (HG.sortList @() @W1))
      boundary = [0 .. 11]
      source = R.PortGraph sorts boundary [HG.Box 's' (map R.Node boundary) []]
      merged interface = R.PortGraph (take 11 sorts) interface []
  left <- either testFailed pure (R.portRule source (merged (0 : [0 .. 10])))
  right <- either testFailed pure (R.portRule source (merged ([0, 1] ++ [1 .. 10])))
  fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) [(False, left), (True, right)] source)
  case fork of
    Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> pure ()
    _ -> testFailed "the two sets of identified boundary positions must disagree"

checkWideDisjointOverlap :: Property ()
checkWideDisjointOverlap = do
  let sorts = concat (replicate 12 (HG.sortList @() @W1))
      boundary = [0 .. 11]
  HG.reifySorts sorts \ @as -> do
    let fragment = HG.unsafeOpenHypergraph @Char @as @'[] sorts boundary []
    remove <- either testFailed pure (fragment [HG.Box 's' boundary []] ==> fragment [])
    overlaps <- either testFailed pure (Completion.hypergraphOverlaps [((), remove)])
    expect "the self-pair has no conflicting matches" 0 (length overlaps)

checkGraphMultiplicities :: Property ()
checkGraphMultiplicities = do
  let atom l = HG.Box l [] []
      source = R.PortGraph [] [] [atom 's']
      target sorts box = R.PortGraph sorts [] (replicate 12 (atom 'a') ++ [box])
      checkBoxes message sorts l r shouldJoin = do
        left <- either testFailed pure (R.portRule source (target sorts l))
        right <- either testFailed pure (R.portRule source (target sorts r))
        fork <- either testFailed pure (Completion.checkPortTemplate (Just 0) [(False, left), (True, right)] source)
        case fork of
          Completion.PortTemplateUnjoinable (Completion.CriticalOverlap False True _ _ _) -> expect message shouldJoin False
          Completion.PortTemplateJoinable 1 -> expect message shouldJoin True
          _ -> testFailed "expected a single fork"
      twoNodes = HG.sortList @() @W2
      wired i o = HG.Box 't' [R.Node i] [R.Node o]
  checkBoxes "different box labels prevent a join" [] (atom 'b') (atom 'c') False
  checkBoxes "the shared input and output node must agree" twoNodes (wired 0 0) (wired 0 1) False
  checkBoxes "renumbering a shared port node preserves the box shape" twoNodes (wired 0 0) (wired 1 1) True
  let marker = HG.box @Char @('[] :: [FINREL]) @'[] 's'
      empty sorts = HG.unsafeOpenHypergraph @Char @('[] :: [FINREL]) @'[] sorts [] [] []
      zero = HG.sortList @FINREL @'[FR Nat0]
      one = HG.sortList @FINREL @'[FR Nat1]
      common = concat (replicate 11 zero)
  someOnes <- either testFailed pure (marker ==> empty (common ++ one))
  allZeros <- either testFailed pure (marker ==> empty (common ++ zero))
  result <- either testFailed pure (Completion.checkHypergraphConfluence (Just 0) [(False, someOnes), (True, allZeros)])
  case result of
    Completion.HypergraphNotLocallyConfluent (Completion.CriticalOverlap False True _ _ _) -> pure ()
    _ -> testFailed "expected the isolated node sorts to prevent a join"

checkDisjointSortedOverlap :: Property ()
checkDisjointSortedOverlap = do
  let zero = HG.sortList @FINREL @'[FR Nat0]
      one = HG.sortList @FINREL @'[FR Nat1]
      sorts = concat (replicate 10 zero)
      boundary = [0 .. length sorts - 1]
  HG.reifySorts sorts \ @as -> do
    let fragment ns = HG.unsafeOpenHypergraph @Char @as @'[] ns boundary []
        empty = fragment sorts []
        isRemoveSelf (Completion.CriticalOverlap left right _ _ _) = not left && not right
    remove <- either testFailed pure (fragment sorts [HG.Box 'p' (take 9 boundary) []] ==> empty)
    forM_ [(zero, True), (one, False)] \(extra, compatible) -> do
      erase <- either testFailed pure (fragment (sorts ++ extra) [HG.Box 'd' boundary []] ==> empty)
      overlaps <- either testFailed pure (Completion.hypergraphOverlaps [(False, remove), (True, erase)])
      case dropWhile isRemoveSelf overlaps of
        Completion.CriticalOverlap left right _ _ _ : _ ->
          expect "the mixed overlap is possible only at the same sort" compatible (left /= right)
        _ -> testFailed "expected at least the deletion rule's self-overlap"

checkDisjointSortedMerge :: Property ()
checkDisjointSortedMerge = do
  let zero = HG.sortList @FINREL @'[FR Nat0]
      one = HG.sortList @FINREL @'[FR Nat1]
      common = concat (replicate 10 zero)
      mergeSorts = common ++ one ++ one
      mergeBoundary = [0 .. length mergeSorts - 1]
      mergedBoundary = [0 .. length common] ++ [length common]
  HG.reifySorts mergeSorts \ @mergePorts -> do
    let fragment = HG.unsafeOpenHypergraph @Char @mergePorts @'[]
        source = fragment mergeSorts mergeBoundary [] [HG.Box 'm' mergeBoundary []]
        target = fragment (common ++ one) mergedBoundary [] []
    merge <- either testFailed pure (source ==> target)
    forM_ [(one, False), (one ++ one, True)] \(extra, compatible) -> do
      let sorts = common ++ extra
          boundary = [0 .. length sorts - 1]
      HG.reifySorts sorts \ @readPorts -> do
        let readFragment = HG.unsafeOpenHypergraph @Char @readPorts @'[] sorts boundary []
        preserve <- either testFailed pure (readFragment [HG.Box 'p' boundary []] ==> readFragment [])
        overlaps <- either testFailed pure (Completion.hypergraphOverlaps [(False, preserve), (True, merge)])
        case overlaps of
          Completion.CriticalOverlap left right _ _ _ : _ ->
            expect "the mixed overlap requires two compatible nodes" compatible (left /= right)
          _ -> testFailed "expected at least the merge rule's self-overlap"

checkHypergraphInterreduction :: Property ()
checkHypergraphInterreduction = do
  let tag = HG.box @Char @W1 @'[]
      a = tag 'a'
      b = tag 'b'
      c = tag 'c'
      d = tag 'd'
      rank label = case label of
        'a' -> 2 :: Int
        'd' -> 2
        'b' -> 1
        _ -> 0
      measure g = let (_, _, _, boxes) = HG.hypergraphParts g in sum (map (rank . HG.label) boxes)
  seeds <- either testFailed pure (sequence [a ==> b, b ==> c, a ==> c, d ==> b])
  result <- either testFailed pure (Completion.completeHypergraph 0 1 (\l r -> compare (measure l) (measure r)) seeds)
  case result of
    Completion.HypergraphComplete final compiled -> do
      expect "a to b is redundant" 3 (length final)
      forM_ [(0, b), (1, a), (2, d)] \(key, source) -> case R.rewritesCompiled compiled source of
        [(actual, reduct)] -> do
          expect "keys are positions in the retained rule list" key actual
          check "the retained rule rewrites directly to c" (HG.isomorphic c reduct)
        _ -> testFailed "expected exactly one retained rule to apply"
    _ -> testFailed "expected interreduction without learning any rules"

data SplitterGenerator = Entry | Split | SplitA | SplitB | A | B | C | D | E
  deriving (Eq)

unary :: SplitterGenerator -> Diagram SplitterGenerator W1 W1
unary = HG.box

splitter :: SplitterGenerator -> Diagram SplitterGenerator W1 W2
splitter = HG.box

-- The rule learned from two splitter reductions overlaps with the downstream rule.
splitterRules :: Either String [R.Rule () SplitterGenerator]
splitterRules =
  sequence
    [ (unary A ** wire) . splitter Split ==> splitter SplitA
    , (wire ** unary B) . splitter Split ==> (wire ** unary C) . splitter SplitB
    , unary D . unary C ==> unary E
    ]

-- Each component is additive under insertion in a diagram context.
diagramOrder :: (a :: HG.OPENHG () SplitterGenerator) ~> b -> a ~> b -> Ordering
diagramOrder l r = compare (measure l) (measure r)
  where
    measure g =
      let (_, _, _, boxes) = HG.hypergraphParts g
          labels = map HG.label boxes
      in ( length (filter (== Entry) labels)
         , length (filter (== Split) labels)
         , length labels
         , length (filter (== SplitB) labels)
         )

completionTests :: TestTree
completionTests =
  testGroup
    "Diagram completion"
    [ testProperty "diagram completion learns a rule that creates the next overlap" completionRounds
    , testProperty "a learned rule simplifies a seed right-hand side" simplifiedRightSide
    ]

completionRounds :: Property ()
completionRounds = do
  initial <- either testFailed pure splitterRules
  oneRound <- either testFailed pure (Completion.completeConvex 1 8 diagramOrder initial)
  () <- case oneRound of
    Completion.ConvexIncomplete partial (Completion.ConvexRuleLimit (Completion.CriticalOverlap first second _ _ _)) -> do
      expect "one learned rule" 4 (length partial)
      expect "the second overlap involves the first learned rule and the downstream rule" [2, 3] (sort [first, second])
    _ -> testFailed "expected a second overlap after the first rule"
  completed <- either testFailed pure (Completion.completeConvex 2 8 diagramOrder initial)
  () <- case completed of
    Completion.ConvexComplete final compiled -> do
      expect "two learned rules" 5 (length final)
      let l = (unary A ** unary E) . splitter SplitB
          r = (wire ** (unary D . unary B)) . splitter SplitA
      result <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled l)
      expect "the second learned rule applies" 1 (R.normalisationRewrites result)
      check "the second learned rule joins the two branches" (HG.isomorphic r (R.normalisedGraph result))
    _ -> testFailed "expected completion with two new rules"
  unoriented <- either testFailed pure (Completion.completeConvex 2 8 (\_ _ -> EQ) initial)
  () <- case unoriented of
    Completion.ConvexIncomplete partial Completion.ConvexUnorientable{} -> expect "the comparison learned no rules" 3 (length partial)
    _ -> testFailed "expected a tie to leave completion unresolved"
  shallow <- either testFailed pure (Completion.completeConvex 2 0 diagramOrder initial)
  case shallow of
    Completion.ConvexIncomplete partial Completion.ConvexJoinLimit{} -> expect "both rules learned before the join limit" 5 (length partial)
    _ -> testFailed "expected the zero-depth check to leave a join unresolved"

simplifiedRightSide :: Property ()
simplifiedRightSide = do
  initial <- either testFailed pure splitterRules
  let entry = splitter Entry
      rhs = (unary A ** unary C) . splitter SplitB
      expected = (wire ** unary B) . splitter SplitA
  seed <- either testFailed pure (entry ==> rhs)
  let seeds = initial ++ [seed]
  before <- either testFailed pure (Completion.compileConvexRules seeds)
  start <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites before rhs)
  expect "the seed right side is initially irreducible" 0 (R.normalisationRewrites start)
  completed <- either testFailed pure (Completion.completeConvex 2 8 diagramOrder seeds)
  case completed of
    Completion.ConvexComplete final compiled -> do
      expect "the earlier rule is retained" 6 (length final)
      result <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled entry)
      expect "entry reaches the simplified target in one step" 1 (R.normalisationRewrites result)
      check "the target agrees with the learned rule" (HG.isomorphic expected (R.normalisedGraph result))
    _ -> testFailed "expected completion and right-hand-side simplification"

data ContextGenerator = F | G | H | Context
  deriving (Eq)

twoWireBox :: ContextGenerator -> Diagram ContextGenerator W2 W2
twoWireBox = HG.box

f :: Diagram ContextGenerator W2 W2
f = twoWireBox F

-- | The non-left-connected example of
-- <https://arxiv.org/html/2109.06049#S6.SS2 String Diagram Rewrite Theory III, §6.2>.
nonLeftConnectedRule :: Either String (R.Rule () ContextGenerator)
nonLeftConnectedRule =
  (f ** wire) . (wire ** crossing) . (f ** wire) ==> f ** (source . sink)
  where
    crossing = swap @_ @(Wire ContextGenerator) @(Wire ContextGenerator)
    sink :: Diagram ContextGenerator W1 '[]
    sink = HG.box G
    source :: Diagram ContextGenerator '[] W1
    source = HG.box H

pathContextTests :: TestTree
pathContextTests =
  testGroup
    "Diagram path contexts"
    [ testProperty "the non-left-connected example is joinable in every maximal path context" $ do
        nlc <- either testFailed pure nonLeftConnectedRule
        let rules = [("NLC1", nlc)]
        result <- either testFailed pure (Completion.checkPathContexts Nothing rules)
        () <- case result of
          -- Two contexts come from (19) and its direct wirings, and 38 from (20).
          Completion.PathContextsJoinable contexts -> expect "number of maximal path contexts" 40 contexts
          Completion.PathContextLimitReached -> testFailed "unexpected depth limit"
          Completion.PathContextNotJoinable{} -> testFailed "a path context failed to join"
        case Completion.checkPathContexts (Just 0) rules of
          Right Completion.PathContextLimitReached -> pure ()
          _ -> testFailed "some pairs need further rewrites to join"
    , testProperty "reports distinct irreducible branches as an unjoinable pair" $ do
        discard <- either testFailed pure (f ==> twoWireBox G)
        retain <- either testFailed pure (f ==> twoWireBox H)
        result <- either testFailed pure (Completion.checkPathContexts (Just 0) [("first", discard), ("second", retain)])
        case result of
          Completion.PathContextNotJoinable (Completion.CriticalOverlap first second _ l r) -> do
            expect "rules in the witness" ("first", "second") (first, second)
            check "the reducts differ" (not (HG.isomorphic l r))
          _ -> testFailed "expected an unjoinable pair"
    , testProperty "convex normalisation skips a match whose path leaves and re-enters it" $ do
        nlc <- either testFailed pure nonLeftConnectedRule
        compiled <- either testFailed pure (Completion.compileConvexRules [nlc])
        let context :: Wire ContextGenerator ~> Wire ContextGenerator
            context = HG.box Context
            host = f . (wire ** context) . f
        expect "ordinary matches" 1 (length (R.rewrites nlc host))
        result <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled host)
        expect "convex rewrites" 0 (R.normalisationRewrites result)
        expect "convex normal form" R.NormalForm (R.normalisationStatus result)
    ]
