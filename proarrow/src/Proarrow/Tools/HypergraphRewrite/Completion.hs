-- | Critical overlaps and bounded Knuth–Bendix-style completion.
-- Convex rewriting works with monogamous acyclic string diagrams and checks
-- all maximal path contexts. Hypergraph completion uses the ordinary matcher
-- with shared Frobenius wiring. Port completion checks schematic overlaps
-- with captured wire sequences.
--
-- See "Proarrow.Tools.KnuthBendix" for completion of typed paths.
module Proarrow.Tools.HypergraphRewrite.Completion
  ( -- * Overlaps and path contexts
    CriticalOverlap (..)
  , criticalOverlaps
  , hypergraphOverlaps
  , HypergraphConfluenceResult (..)
  , checkHypergraphConfluence
  , PathContextResult (..)
  , checkPathContexts

    -- * Variadic overlaps
  , portOverlapTemplates
  , parameterPortOverlapTemplates
  , PortTemplateResult (..)
  , MappedPortFork (..)
  , checkPortTemplate
  , PortSymmetry (..)
  , checkPortTemplateWithSymmetry
  , checkPortTemplateWithScalars

    -- * Variadic completion
  , orientPortOverlap
  , orientParameterPortOverlap
  , PortCompletion (..)
  , PortCompletionStop (..)
  , PortCompletionOptions (..)
  , completePorts
  , PortComparison (..)
  , ParameterPortOptions (..)
  , parameterPortOptions
  , completeParameterPorts

    -- * Convex rewriting and completion
  , withFixedRule
  , ConvexRules
  , compileConvexRules
  , normaliseConvex
  , ConvexCompletion (..)
  , ConvexCompletionStop (..)
  , completeConvex

    -- * Hypergraph completion
  , HypergraphCompletion (..)
  , HypergraphCompletionStop (..)
  , completeHypergraph
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, guard, unless, void, when)
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Type)
import Data.List (tails)
import Data.List qualified as List
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe, maybeToList)
import Data.Typeable (Typeable)
import Numeric.Natural (Natural)
import Prelude

import Proarrow.Category.Instance.FinHask (unionFind)
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , OPENHG
  , Wires
  , reifySorts
  , sameSort
  , unsafeOpenHypergraph
  )
import Proarrow.Core (CategoryOf (..), Kind)
import Proarrow.Object (SomeOf (..))
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Tools.HypergraphRewrite
  ( CompiledRules
  , NormalisationResult (..)
  , NormalisationStatus (NormalForm)
  , RewriteLimits (..)
  , compileRules
  )
import Proarrow.Tools.HypergraphRewrite.Internal
  ( CaptureEnd (..)
  , Graph (..)
  , LabelTest (..)
  , Match
  , Parameter (Literal, Variable)
  , Port (..)
  , PortGraph (..)
  , PortReplacement (..)
  , PortSymmetry (..)
  , Prepared
  , Rule (..)
  , checkPortLeft
  , deletedImages
  , graph
  , internalNodes
  , mapLabels
  , mapPortLabels
  , matches
  , nonConflictingBy
  , normaliseBy
  , normaliseGraphBy
  , parameterPortRule
  , parameterPortVariants
  , portRule
  , replaceMany
  , rule
  , sameGraph
  , symmetricInputs
  , symmetricOutputs
  , traverseLabels
  )
import Proarrow.Tools.HypergraphRewrite.Internal.Matcher
  ( compiledHasPortMaps
  , compiledMatches
  , compiledMatchesAvoiding
  , compiledMatchesWithMaps
  )

-- | Two one-step reductions of a common diagram. The rule keys identify the
-- two steps. The source and both reducts share an ordered boundary.
type CriticalOverlap :: Type -> Kind -> Type -> Type
data CriticalOverlap key s l where
  CriticalOverlap
    :: forall {key} {s} {l} as bs
     . key
    -> key
    -> Wires @s @l as ~> Wires @s @l bs
    -> Wires @s @l as ~> Wires @s @l bs
    -> Wires @s @l as ~> Wires @s @l bs
    -> CriticalOverlap key s l

-- | Construct the overlapping pre-critical pairs of fixed, left-connected
-- string-diagram rules. The sides must have acyclic, monogamous wiring, and
-- every input of a left-hand side must reach every output. Rule instances with
-- captures or parameters are outside this fragment. Parallel disjoint steps
-- commute and are omitted. Boundaries are ordered by node number.
-- See <https://arxiv.org/html/2109.06049#S5.SS4 String Diagram Rewrite Theory III, §5.4>.
criticalOverlaps :: (Eq l, DecidableIso s) => [(key, Rule s l)] -> Either String [CriticalOverlap key s l]
criticalOverlaps rules = do
  patterns <- traverse fixedRule rules
  unless
    (all leftConnected patterns)
    (Left "criticalOverlaps: every left input must reach every left output")
  pure [renderOverlap host left right | (host, left, right) <- preCriticalPairs (StringOverlaps False) patterns]
  where
    leftConnected (_, Graph _ ins outs bs, _) =
      let edges = wireEdges bs
      in all (\i -> all (`IS.member` reachableNodes edges i) outs) ins

-- | Enumerate overlaps of fixed literal hypergraph rules under the ordinary
-- matcher. Glue compatible box occurrences and their ports, then consider
-- additional sort-preserving node identifications. Retain pairs that share a
-- box, delete a node used by the other match, or identify two nodes of the
-- other match in a replacement. Each witness exposes the nodes preserved by
-- both steps as inputs, in node order.
hypergraphOverlaps :: (Eq l, DecidableIso s) => [(key, Rule s l)] -> Either String [CriticalOverlap key s l]
hypergraphOverlaps rules = do
  patterns <- traverse literalRule rules
  pure [renderOverlap host left right | (host, left, right) <- preCriticalPairs HypergraphOverlaps patterns]

-- | The outcome of checking local confluence for single-step hypergraph
-- rewriting. Success counts the overlaps checked. Failure returns a fork
-- whose branches have disjoint sets of reducts, and a depth limit returns an
-- unresolved fork.
type HypergraphConfluenceResult :: Type -> Kind -> Type -> Type
data HypergraphConfluenceResult key s l
  = HypergraphLocallyConfluent Int
  | HypergraphNotLocallyConfluent (CriticalOverlap key s l)
  | HypergraphConfluenceLimit (CriticalOverlap key s l)

-- | Check local confluence of fixed literal rules with unique keys. The depth
-- bound applies separately to each side of an overlap. Use @Nothing@ for an
-- unbounded search, which can diverge on a nonterminating system.
--
-- Any two matches in a host restrict to their union. A host boundary port or
-- an outside box can meet that union only at a node preserved by both steps.
-- Those nodes are exactly the boundary exposed by 'hypergraphOverlaps'. A
-- joining derivation tracks each attachment through the boundary map, so it
-- lifts back into the host. Even when it merges two boundary nodes, adding back the
-- context leaves the current overlap graph embedded injectively: the context
-- started with a distinct node for each attachment. Omitted pairs commute
-- because their boxes and deletions do not interfere and neither replacement
-- folds the other match. See the clipping and embedding argument in
-- <https://arxiv.org/html/2109.06049#S3 String Diagram Rewrite Theory III, §3>.
--
-- This check concerns the single-step relation of
-- 'Proarrow.Tools.HypergraphRewrite.rewritesCompiled'. For a terminating
-- system, local confluence implies confluence.
checkHypergraphConfluence
  :: (Ord key, Eq l, DecidableIso s)
  => Maybe Natural -> [(key, Rule s l)] -> Either String (HypergraphConfluenceResult key s l)
checkHypergraphConfluence maxDepth rules = do
  patterns <- traverse literalRule rules
  compiled <- compileRules rules
  pure $ case checkHypergraphPairs maxDepth (map snd . compiledMatches compiled) patterns of
    AllJoinable count -> HypergraphLocallyConfluent count
    Unjoinable (host, left, right) -> HypergraphNotLocallyConfluent (renderOverlap host left right)
    JoinLimit (host, left, right) -> HypergraphConfluenceLimit (renderOverlap host left right)

-- | The result of checking all pairs of symbolic steps from a supplied
-- template. Witnesses represent each named sequence by one extra input node
-- after the template's explicit boundary, in first-occurrence order.
data PortTemplateResult key l
  = PortTemplateJoinable Int
  | PortTemplateUnjoinable (CriticalOverlap key () l)
  | PortTemplateJoinLimit (CriticalOverlap key () l)
  | PortTemplateMappedUnjoinable (MappedPortFork key l)
  | PortTemplateMappedJoinLimit (MappedPortFork key l)

-- | The overlap gives the cores. Each branch carries its maps by capture
-- name, ordered from the original boundary towards the core.
data MappedPortFork key l
  = MappedPortFork (CriticalOverlap key () l) [(String, [Box l CaptureEnd])] [(String, [Box l CaptureEnd])]

-- | Check the forks of a schematic source with unit-sorted wires. Fixed
-- replacements may refer to explicit interface nodes, fresh numbered nodes
-- or whole captures. Interface positions may be identified in a replacement.
-- Label parameters are evaluated in the label type of the caller-supplied source.
--
-- Each sequence is represented by a distinct protected boundary node. A
-- numbered port cannot match a sequence marker, even at the rule interface.
-- Captures may consume entire markers, and fixed replacements copy their
-- sequences in order. A computed replacement can be applied when every
-- capture contains only numbered wires, so the lengths and individual ports
-- are known. Consequently a symbolic join lifts to any substitution
-- of the markers by port sequences (including empty sequences and aliases),
-- provided those ports stay outside the template's numbered nodes. Any
-- numbered nodes introduced along the derivation are fresh for the substitution.
-- The result concerns the forks represented this way in the supplied template.
-- Concrete instances may have additional matches, including computed
-- replacements whose captures include sequence markers in the template.
-- Pointwise maps on sequences with one occurrence participate in forks and
-- can be carried along their boundary positions while checking joins.
checkPortTemplate
  :: (Eq l) => Maybe Natural -> [(key, Rule () l)] -> PortGraph () l -> Either String (PortTemplateResult key l)
checkPortTemplate = checkPortTemplateWith (const OrderedPorts) sameGraph

-- | Turn an unjoinable symbolic fork into a literal port rule. The input
-- template supplies the names and order of the sequences in the witness.
-- The ordering must strictly decrease after every allowed capture
-- substitution, including empty sequences. Orientation rejects a rule
-- whose two sides are isomorphic with all captures empty. The resulting
-- rule uses the labels from the witness. The rule can factor through one
-- port per left interface node if the right branch preserves every left
-- identification and the factored rule still decreases. The right branch
-- may identify additional positions. Adjacent captures that occur once and
-- stay together in the same order can become a single capture.
orientPortOverlap
  :: (Eq l)
  => (PortGraph () l -> PortGraph () l -> Ordering)
  -> PortGraph () l
  -> PortTemplateResult key l
  -> Either String (Rule () l)
orientPortOverlap = orientPortOverlapWith portRule

-- | Orient a symbolic fork into a parameterized port rule. The caller
-- converts values from the symbolic algebra into label parameters. Variables
-- must use the same names in both branches. The oriented left side can only
-- contain variables and literals, and the right side can compute expressions
-- from the variables bound on the left. The comparison follows the ordering
-- requirements of 'completeParameterPorts'.
orientParameterPortOverlap
  :: (Traversable f, Typeable f, Eq (f ()), Eq (f symbolic), Eq a)
  => (symbolic -> Parameter a)
  -> (PortGraph () (f symbolic) -> PortGraph () (f symbolic) -> Ordering)
  -> PortGraph () (f symbolic)
  -> PortTemplateResult key (f symbolic)
  -> Either String (Rule () (f a))
orientParameterPortOverlap parameter = orientPortOverlapWith (reifyPortRule parameter)

reifyPortRule
  :: (Traversable f, Typeable f, Eq (f ()), Eq a)
  => (symbolic -> Parameter a)
  -> PortGraph () (f symbolic)
  -> PortGraph () (f symbolic)
  -> Either String (Rule () (f a))
reifyPortRule parameter left right =
  parameterPortRule (mapPortLabels (fmap parameter) left) (mapPortLabels (fmap parameter) right)

orientPortOverlapWith
  :: (Eq l)
  => (PortGraph () l -> PortGraph () l -> Either String (Rule () m))
  -> (PortGraph () l -> PortGraph () l -> Ordering)
  -> PortGraph () l
  -> PortTemplateResult key l
  -> Either String (Rule () m)
orientPortOverlapWith build order source (PortTemplateUnjoinable (CriticalOverlap _ _ host left right)) = do
  symbolic <- symbolicPortGraph source
  unless (sameGraph symbolic (graph host)) (Left "orientPortOverlap: the witness does not match the supplied template")
  (l, r) <- orientPortBranches (const OrderedPorts) order source (graph left) (graph right)
  build l r
orientPortOverlapWith _ _ _ PortTemplateMappedUnjoinable{} =
  Left "orientPortOverlap: the fork carries pointwise boundary maps"
orientPortOverlapWith _ _ _ _ = Left "orientPortOverlap: expected an unjoinable fork"

orientPortBranches
  :: (Eq l)
  => (l -> PortSymmetry)
  -> (PortGraph () l -> PortGraph () l -> Ordering)
  -> PortGraph () l
  -> Graph () l
  -> Graph () l
  -> Either String (PortGraph () l, PortGraph () l)
orientPortBranches symmetry order source@(PortGraph _ sourceBoundary _) left right = do
  let branch = restorePortSequences (length sourceBoundary) (portSequenceNames source)
  (l, r) <- coalescePortCaptures (const OrderedPorts) <$> branch left <*> branch right
  case order l r of
    GT -> finish l r
    LT -> finish r l
    EQ -> Left "orientPortOverlap: the branches have equal rank"
  where
    finish l r = do
      let (l', r') = coalescePortCaptures symmetry l r
      unless (order l' r' == GT) (Left "orientPortOverlap: the coalesced rule does not decrease")
      (lhs, rhs) <- factor l' r'
      when (not (null (portSequenceNames lhs)) && sameGraph (emptyCaptures lhs) (emptyCaptures rhs)) $
        Left "orientPortOverlap: empty captures make the rule a no-op"
      pure (lhs, rhs)
    emptyCaptures (PortGraph ns boundary boxes) =
      Graph ns boundary [] [Box l (mapMaybe numbered ins) (mapMaybe numbered outs) | Box l ins outs <- boxes]
    numbered (Node n) = Just n
    numbered _ = Nothing
    factor l@(PortGraph ls li lb) r@(PortGraph rs ri rb)
      | length li == leftCount = Right (l, r)
      | length pairs /= leftCount =
          Left "orientPortOverlap: the right branch splits a left interface wire"
      | order l' r' == GT = Right (l', r')
      | otherwise = Left "orientPortOverlap: the factored rule does not decrease"
      where
        leftCount = length (nubOrd li)
        pairs = nubOrd (zip li ri)
        l' = PortGraph ls (map fst pairs) lb
        r' = PortGraph rs (map snd pairs) rb

coalescePortCaptures :: (l -> PortSymmetry) -> PortGraph () l -> PortGraph () l -> (PortGraph () l, PortGraph () l)
coalescePortCaptures symmetry left right = case List.find mergeable leftPairs of
  Just (a, b) -> coalescePortCaptures symmetry (replace (const OrderedPorts) a b left) (replace symmetry a b right)
  Nothing -> (left, right)
  where
    -- Both sides see the same concatenation, so any assignment to the new
    -- capture is covered by taking the second sequence empty. A symmetric
    -- replacement port list can first bring the two sequences together.
    leftPairs = concatMap adjacent (lists left)
    rightLists = [(symmetric, ps) | box <- diagramBoxes right, (symmetric, ps) <- portLists symmetry box]
    mergeable pair@(a, b) =
      all onceInBoth [a, b] && any supports rightLists
      where
        supports (symmetric, ps)
          | symmetric = Capture a `elem` ps && Capture b `elem` ps
          | otherwise = pair `elem` adjacent ps
    onceInBoth n = count n left == 1 && count n right == 1
    count n g = length [() | ps <- lists g, Capture name <- ps, name == n]
    adjacent ps = [(a, b) | (Capture a, Capture b) <- zip ps (drop 1 ps)]
    lists = concatMap (\box -> [inputs box, outputs box]) . diagramBoxes
    diagramBoxes (PortGraph _ _ boxes) = boxes
    portLists policyFor (Box l i o) =
      let policy = policyFor l in [(symmetricInputs policy, i), (symmetricOutputs policy, o)]
    replace policyFor a b (PortGraph ns boundary boxes) = PortGraph ns boundary (map change boxes)
      where
        change (Box l i o) =
          let policy = policyFor l
          in Box l (mergeList (symmetricInputs policy) i) (mergeList (symmetricOutputs policy) o)
        belongs p = p == Capture a || p == Capture b
        mergeList symmetric ps
          | symmetric && Capture a `elem` ps && Capture b `elem` ps =
              let (before, after) = break belongs ps in before ++ Capture a : filter (not . belongs) after
          | otherwise = merge ps
        merge (Capture x : Capture y : rest) | x == a && y == b = Capture a : rest
        merge (p : rest) = p : merge rest
        merge [] = []

-- | Like 'checkPortTemplate', allowing permutations of the indicated ports
-- when testing whether branches meet. Boundary order and port multiplicity
-- are preserved. The search still applies the supplied rules to ordered
-- ports and uses exact isomorphism to identify visited states.
checkPortTemplateWithSymmetry
  :: (Eq l)
  => (l -> PortSymmetry)
  -> Maybe Natural
  -> [(key, Rule () l)]
  -> PortGraph () l
  -> Either String (PortTemplateResult key l)
checkPortTemplateWithSymmetry symmetry = checkPortTemplateWith symmetry (sameGraphWithSymmetry symmetry)

-- | Compare reducts up to port symmetries and products of nullary scalars.
-- The classifier selects scalar labels and supplies their values in a
-- commutative monoid. A label with ports remains part of the graph. Scalar
-- products affect only the comparison between branches.
checkPortTemplateWithScalars
  :: (Eq l, Eq m, Monoid m)
  => (l -> PortSymmetry)
  -> (l -> Maybe m)
  -> Maybe Natural
  -> [(key, Rule () l)]
  -> PortGraph () l
  -> Either String (PortTemplateResult key l)
checkPortTemplateWithScalars symmetry scalar = checkPortTemplateWith symmetry (sameGraphWithScalars symmetry scalar)

sameGraphWithScalars
  :: (Eq l, Eq m, Monoid m) => (l -> PortSymmetry) -> (l -> Maybe m) -> Graph () l -> Graph () l -> Bool
sameGraphWithScalars symmetry scalar left right =
  let (leftProduct, l) = separate left
      (rightProduct, r) = separate right
  in leftProduct == rightProduct && sameGraphWithSymmetry symmetry l r
  where
    separate (Graph sorts ins outs boxes) =
      let (factor, ordinary) = foldr split (mempty, []) boxes
      in (factor, Graph sorts ins outs ordinary)
    split (Box l [] []) (factor, boxes) | Just value <- scalar l = (value <> factor, boxes)
    split box (factor, boxes) = (factor, box : boxes)

checkPortTemplateWith
  :: (Eq l)
  => (l -> PortSymmetry)
  -> (Graph () l -> Graph () l -> Bool)
  -> Maybe Natural
  -> [(key, Rule () l)]
  -> PortGraph () l
  -> Either String (PortTemplateResult key l)
checkPortTemplateWith symmetry equivalent maxDepth rules source = do
  unless
    (all (isJust . overlapReplacement . snd) rules)
    ( Left
        "checkPortTemplate: expected port rules with computed replacements or fixed replacements using numbered nodes and whole captures"
    )
  let (keys, patterns) = unzip rules
  compiled <- compileRules (zip [0 :: Int ..] patterns)
  checkCompiledPortTemplate symmetry equivalent maxDepth (keys !!) compiled source

checkCompiledPortTemplate
  :: (Eq l)
  => (l -> PortSymmetry)
  -> (Graph () l -> Graph () l -> Bool)
  -> Maybe Natural
  -> (Int -> key)
  -> CompiledRules Int () l
  -> PortGraph () l
  -> Either String (PortTemplateResult key l)
checkCompiledPortTemplate symmetry equivalent maxDepth key compiled source = do
  host <- symbolicPortGraph source
  let PortGraph _ boundary _ = source
      boundarySize = length boundary
      names = portSequenceNames source
      useMaps = not (null names) && compiledHasPortMaps compiled
      next = portSteps useMaps boundarySize compiled
      steps = [(key i, target) | (i, target) <- next (host, IM.empty)]
      forks = [(left, right) | left : rest <- tails steps, right <- rest]
      witness ((lk, (left, leftMaps)), (rk, (right, rightMaps))) = withDiagramBoundary host \render ->
        let core = CriticalOverlap lk rk (render host) (render left) (render right)
            named paths = [(names !! i, boxes) | (i, boxes) <- IM.toAscList paths]
        in if IM.null leftMaps && IM.null rightMaps
             then Left core
             else Right (MappedPortFork core (named leftMaps) (named rightMaps))
      compareStates sameMaps sameCore (left, leftMaps) (right, rightMaps) =
        sameMaps leftMaps rightMaps && sameCore left right
      join =
        joinGraphsBy (compareStates (==) sameGraph) (compareStates (samePortMaps symmetry) equivalent) maxDepth (map snd . next)
  pure $ case checkJoins join (\((_, l), (_, r)) -> (l, r)) forks of
    AllJoinable count -> PortTemplateJoinable count
    Unjoinable fork -> either PortTemplateUnjoinable PortTemplateMappedUnjoinable (witness fork)
    JoinLimit fork -> either PortTemplateJoinLimit PortTemplateMappedJoinLimit (witness fork)

symbolicMatches :: (Eq l) => Int -> CompiledRules key () l -> Graph () l -> [(Int, Prepared () l)]
symbolicMatches boundarySize compiled host@(Graph _ inputs' _ _) =
  compiledMatchesAvoiding (IS.fromList (drop boundarySize inputs')) compiled host

type PortState :: Type -> Type
type PortState l = (Graph () l, IM.IntMap [Box l CaptureEnd])

samePortMaps
  :: (Eq l)
  => (l -> PortSymmetry)
  -> IM.IntMap [Box l CaptureEnd]
  -> IM.IntMap [Box l CaptureEnd]
  -> Bool
samePortMaps symmetry left right = left == right || normalisePaths left == normalisePaths right
  where
    -- Keep the capture, the path order and each endpoint. Only the ports
    -- within an individual symmetric input or output list may move.
    normalisePaths = fmap (map orderPorts)
    orderPorts (Box l ins outs) =
      let policy = symmetry l
      in Box l (if symmetricInputs policy then List.sort ins else ins) (if symmetricOutputs policy then List.sort outs else outs)

-- The core keeps its sequence marker. Equal maps can be reattached at the
-- boundary once the cores join.
portSteps
  :: (Eq l)
  => Bool
  -> Int
  -> CompiledRules key () l
  -> PortState l
  -> [(Int, PortState l)]
portSteps useMaps boundarySize compiled (core@(Graph _ boundary _ _), outer) =
  [ (i, (replaceMany lhs rhs core [match], foldl' add outer maps))
  | (i, ((lhs, rhs, match), maps)) <- steps
  ]
  where
    steps
      | useMaps = compiledMatchesWithMaps (IM.keysSet markers) compiled core
      | otherwise = map (fmap (,[])) (symbolicMatches boundarySize compiled core)
    markers = IM.fromList (zip (drop boundarySize boundary) [0 ..])
    add paths (node, box) = IM.insertWith (flip (++)) (markers IM.! node) [box] paths

-- | Bounded completion of port rules on the generated templates.
-- The returned rules are in input and discovery order.
data PortCompletion l
  = PortComplete [Rule () l] (CompiledRules Int () l)
  | PortIncomplete [Rule () l] (PortCompletionStop l)

-- | The unresolved template and its fork. Keys index the returned rules.
data PortCompletionStop l
  = PortRuleLimit (PortGraph () l) (CriticalOverlap Int () l)
  | PortJoinLimit (PortGraph () l) (CriticalOverlap Int () l)
  | PortUnorientable String (PortGraph () l) (CriticalOverlap Int () l)
  | PortMappedRuleLimit (PortGraph () l) (MappedPortFork Int l)
  | PortMappedUnorientable (PortGraph () l) (MappedPortFork Int l)
  | PortMappedJoinLimit (PortGraph () l) (MappedPortFork Int l)

-- | Bounds on rule learning and the search depth from either branch, and the
-- ordering used to orient the simplified branches of a fork. The order must
-- be well-founded and preserved by contexts and parameter substitution.
-- Seed and learned rules must strictly decrease, including when captures
-- are empty.
data PortCompletionOptions l = PortCompletionOptions
  { maxLearnedRules :: Natural
  , maxJoinDepth :: Natural
  , portReductionOrder :: PortGraph () l -> PortGraph () l -> Ordering
  }

-- | Complete fixed literal port rules on the generated templates under the
-- symbolic semantics of 'checkPortTemplate'. A learned rule is rejected if
-- setting all captures to empty makes it a no-op.
completePorts
  :: (Eq l)
  => PortCompletionOptions l
  -> [Rule () l]
  -> Either String (PortCompletion l)
completePorts options rules =
  fst
    <$> completePortsWith
      CompareOrderedPorts
      portOverlapTemplates
      (\l r -> (,()) . (: []) <$> portRule l r)
      options
      rules

-- | Compare branches by ordered graph isomorphism, or up to port symmetry
-- and products of nullary scalars as in 'checkPortTemplateWithScalars'.
-- Declared symmetries must hold under parameter substitution. Completion can
-- use them to bring captures together on a replacement box.
data PortComparison l where
  CompareOrderedPorts :: PortComparison l
  ComparePortScalars :: (Eq m, Monoid m) => (l -> PortSymmetry) -> (l -> Maybe m) -> PortComparison l

-- | The parameter algebra and the policies used to compare and emit rules.
data ParameterPortOptions f symbolic concrete = ParameterPortOptions
  { freshParameter :: Int -> symbolic
  -- ^ Fresh variables for generating overlaps.
  , symbolicParameter :: symbolic -> Parameter symbolic
  -- ^ Reify a symbolic value for further rounds of completion.
  , concreteParameter :: symbolic -> Parameter concrete
  -- ^ Reify the same value in the concrete algebra.
  , portComparison :: PortComparison (f symbolic)
  , matchingPortSymmetry :: f () -> PortSymmetry
  -- ^ Expand fixed port lists as in 'parameterPortVariants'. A symmetric
  -- list with one capture can also distribute it across the numbered gaps.
  , reparameterise :: [symbolic] -> [symbolic] -> symbolic -> symbolic
  -- ^ An algebraic change of variables given the oriented left and right
  -- parameters. The returned map applies to both branches and must
  -- preserve the equation for all parameter values.
  }

-- | Use exact comparison and keep port lists and parameters as learned.
parameterPortOptions
  :: (Int -> symbolic)
  -> (symbolic -> Parameter symbolic)
  -> (symbolic -> Parameter concrete)
  -> ParameterPortOptions f symbolic concrete
parameterPortOptions fresh symbolic concrete =
  ParameterPortOptions fresh symbolic concrete CompareOrderedPorts (const OrderedPorts) (\_ _ -> id)

-- | Complete rules in a symbolic parameter algebra and also emit the learned
-- rules in a concrete algebra. The reifiers must preserve variable names and
-- interpret the same expressions in both algebras. The returned rules are in
-- discovery order, including those learned before a bounded stop. Append them
-- to the corresponding concrete seed rules to use the same priorities.
--
-- One learned equation uses one budget slot and emits all its ordered
-- variants. To orient a fork with pointwise boundary maps, the normalised
-- branches must carry equal maps and the current rules must reduce each map
-- preceded by its reflection to a wire.
completeParameterPorts
  :: forall f symbolic a
   . (Traversable f, Typeable f, Eq (f ()), Eq (f symbolic), Eq symbolic, Eq a)
  => ParameterPortOptions f symbolic a
  -> PortCompletionOptions (f symbolic)
  -> [Rule () (f symbolic)]
  -> Either String (PortCompletion (f symbolic), [Rule () (f a)])
completeParameterPorts ParameterPortOptions{..} options rules = do
  (result, concreteRules) <-
    completePortsWith portComparison (parameterPortOverlapTemplates freshParameter) build options rules
  emitted <- concat <$> sequence concreteRules
  pure (result, emitted)
  where
    build left right = do
      let relabel = mapPortLabels (fmap (reparameterise (values left) (values right)))
          (l, r) = spreadSymmetricCaptures (matchingPortSymmetry . void) (relabel left) (relabel right)
      unless
        (portReductionOrder options l r == GT)
        (Left "completeParameterPorts: the reparameterised rule does not decrease")
      learned <- emit symbolicParameter l r
      pure (learned, emit concreteParameter l r)
    emit
      :: (Eq b)
      => (symbolic -> Parameter b) -> PortGraph () (f symbolic) -> PortGraph () (f symbolic) -> Either String [Rule () (f b)]
    emit parameter l r = reifyPortRule parameter l r >>= parameterPortVariants matchingPortSymmetry
    values (PortGraph _ _ boxes) = concatMap (toList . label) boxes

-- By symmetry, a single capture can be moved past any numbered port in its
-- list. Give each gap its own capture and concatenate the pieces on the right.
spreadSymmetricCaptures
  :: (l -> PortSymmetry) -> PortGraph s l -> PortGraph s l -> (PortGraph s l, PortGraph s l)
spreadSymmetricCaptures symmetry left@(PortGraph ls li lb) right@(PortGraph rs ri rb)
  | M.null splits = (left, right)
  | otherwise = (PortGraph ls li (map spreadBox lb), PortGraph rs ri (map spliceBox rb))
  where
    names = [name | Box _ ins outs <- lb, Capture name <- ins ++ outs]
    counts = M.fromListWith (+) [(name, 1 :: Int) | name <- names]
    prefix = until (\p -> not (any (List.isPrefixOf p) names)) ('_' :) "gap:"
    splits =
      M.fromList
        [ (name, [Capture (prefix ++ name ++ ":" ++ show i) | i <- [0 .. length ps - 1]])
        | Box l ins outs <- lb
        , (True, ps) <- [(symmetricInputs (symmetry l), ins), (symmetricOutputs (symmetry l), outs)]
        , length ps > 1
        , [name] <- [[n | Capture n <- ps]]
        , M.lookup name counts == Just 1
        ]
    spreadBox (Box l ins outs) = Box l (spread ins) (spread outs)
    spread ps = case [gaps | Capture name <- ps, Just gaps <- [M.lookup name splits]] of
      [gaps] -> concat (zipWith (:) gaps ([[p] | p@Node{} <- ps] ++ [[]]))
      _ -> ps
    spliceBox (Box l ins outs) = Box l (concatMap splice ins) (concatMap splice outs)
    splice p@(Capture name) = M.findWithDefault [p] name splits
    splice p = [p]

completePortsWith
  :: (Eq l)
  => PortComparison l
  -> ([Rule () l] -> Either String [PortGraph () l])
  -> (PortGraph () l -> PortGraph () l -> Either String ([Rule () l], a))
  -> PortCompletionOptions l
  -> [Rule () l]
  -> Either String (PortCompletion l, [a])
completePortsWith comparison overlaps build (PortCompletionOptions maxRules maxDepth order) = go maxRules []
  where
    (symmetry, equivalent) = case comparison of
      CompareOrderedPorts -> (const OrderedPorts, sameGraph)
      ComparePortScalars policy scalar -> (policy, sameGraphWithScalars policy scalar)
    depth = Just maxDepth
    go budget learnedRev rules = do
      templates <- overlaps rules
      compiled <- compileRules (zip [0 ..] rules)
      let finish result = Right (result, reverse learnedRev)
          incomplete = finish . PortIncomplete rules
          check limited [] = finish (maybe (PortComplete rules compiled) (PortIncomplete rules) limited)
          check limited (source : rest) = do
            result <- checkCompiledPortTemplate symmetry equivalent depth id compiled source
            case result of
              PortTemplateJoinable _ -> check limited rest
              PortTemplateJoinLimit fork -> check (limited <|> Just (PortJoinLimit source fork)) rest
              PortTemplateMappedJoinLimit fork -> check (limited <|> Just (PortMappedJoinLimit source fork)) rest
              PortTemplateMappedUnjoinable mapped@(MappedPortFork fork leftMaps rightMaps)
                | budget == 0 -> incomplete (PortMappedRuleLimit source mapped)
                | otherwise -> case learn source fork leftMaps rightMaps of
                    Left _ -> incomplete (PortMappedUnorientable source mapped)
                    Right (learned, emitted) -> go (budget - 1) (emitted : learnedRev) (rules ++ learned)
              PortTemplateUnjoinable fork
                | budget == 0 -> incomplete (PortRuleLimit source fork)
                | otherwise -> case learn source fork [] [] of
                    Left err -> incomplete (PortUnorientable err source fork)
                    Right (learned, emitted) -> go (budget - 1) (emitted : learnedRev) (rules ++ learned)
          learn source@(PortGraph _ boundary _) (CriticalOverlap _ _ _ left right) leftMaps rightMaps = do
            let names = portSequenceNames source
                useMaps = not (null names) && compiledHasPortMaps compiled
                next = map snd . portSteps useMaps (length boundary) compiled
                same (l, lm) (r, rm) = lm == rm && sameGraph l r
                normalForm diagram maps =
                  maybe
                    (Left "completePorts: could not normalise both branches within the depth limit")
                    Right
                    ( normalFormWithinBy
                        same
                        maxDepth
                        next
                        (diagram, IM.fromList [(i, path) | (i, n) <- zip [0 ..] names, Just path <- [lookup n maps]])
                    )
            (l, lm) <- normalForm (graph left) leftMaps
            (r, rm) <- normalForm (graph right) rightMaps
            unless (samePortMaps symmetry lm rm && all (canCancelPath equivalent maxDepth compiled) lm) $
              Left "completePorts: could not cancel the pointwise boundary maps"
            (lhs, rhs) <- orientPortBranches symmetry order source l r
            result@(learned, _) <- build lhs rhs
            _ <- overlaps learned
            pure result
      check Nothing templates

-- Adding the reflected path outside the common path must reduce to a wire.
-- The resulting left inverse justifies removing the path on every captured leg.
canCancelPath
  :: (Eq l)
  => (Graph () l -> Graph () l -> Bool)
  -> Natural
  -> CompiledRules Int () l
  -> [Box l CaptureEnd]
  -> Bool
canCancelPath equivalent maxDepth compiled path =
  joinGraphsBy sameGraph equivalent (Just maxDepth) next composed wire == Just True
  where
    next = singleReducts (map snd . compiledMatches compiled)
    flipEnd Outer = Inner
    flipEnd Inner = Outer
    chain = map (fmap flipEnd) (reverse path) ++ path
    at n Outer = n
    at n Inner = n + 1
    composed = Graph (replicate (length chain + 1) (Some @'())) [0, length chain] [] (zipWith (fmap . at) [0 ..] chain)
    wire = Graph [Some @'()] [0, 0] [] []

data SymmetryLabel l = OriginalBox l | InputLeg | OutputLeg
  deriving (Eq)

sameGraphWithSymmetry :: (Eq l) => (l -> PortSymmetry) -> Graph () l -> Graph () l -> Bool
sameGraphWithSymmetry symmetry left right =
  sameGraph (encode left) (encode right)
  where
    -- Identical legs incident to a private hub encode a multiset of ports.
    -- The ordered boundary is copied directly, so its node map is fixed
    -- before the isomorphism search compares any legs.
    encode (Graph sorts ins outs boxes) =
      let (end, expanded) = List.mapAccumL encodeBox (length sorts) boxes
      in Graph (sorts ++ replicate (end - length sorts) (Some @'())) ins outs (concat expanded)
    encodeBox start (Box label' ins outs) =
      let order = symmetry label'
          symIn = symmetricInputs order
          symOut = symmetricOutputs order
          (afterInputs, ins', inputLegs)
            | symIn = (start + 1, [start], [Box InputLeg [i] [start] | i <- ins])
            | otherwise = (start, ins, [])
          (end, outs', outputLegs)
            | symOut = (afterInputs + 1, [afterInputs], [Box OutputLeg [afterInputs] [o] | o <- outs])
            | otherwise = (afterInputs, outs, [])
      in (end, Box (OriginalBox label') ins' outs' : inputLegs ++ outputLegs)

-- | Enumerate schematic sources where two literal port rules share one or two
-- boxes, or share interface wires that one rule can merge and the other needs
-- to keep distinct. Each left port list allows at most one capture in each gap between numbered ports,
-- including before the first port and after the last. Each capture must occur
-- once on the left, and every numbered node must occur at a box port.
-- Captures stand for external leg sequences.
--
-- A numbered port can align with another numbered port or occupy a capture
-- on the other side. A deleted node must stay within the deleting match and
-- cannot also occur in one of that match's captures. Preserved nodes can
-- be identified even when they do not meet at a shared port. Numbered nodes
-- preserved by both matches are exposed as the template's boundary.
-- Retain a common symbolic sequence wherever both lists allow a capture.
-- Different embeddings can give the same template.
-- Pass the generated sources to 'checkPortTemplate' to check their joins.
portOverlapTemplates :: (Eq l) => [Rule () l] -> Either String [PortGraph () l]
portOverlapTemplates =
  portOverlapTemplatesBy "literal labels" literalPortPattern (==) (\_ -> Just . map (either id id))

-- | Generate overlaps from rules built with
-- 'Proarrow.Tools.HypergraphRewrite.parameterPortRule',
-- 'Proarrow.Tools.HypergraphRewrite.parameterPortRuleWith', or
-- 'Proarrow.Tools.HypergraphRewrite.parameterPortRuleMap'. Shared boxes unify
-- their label parameters. Literal constraints propagate to every occurrence
-- of the same variable in its rule, and conflicting constraints discard the
-- overlap. Supply a distinct symbolic value for each free variable class,
-- disjoint from the literal values in the rules.
-- Computed replacements can overlap when the template fixes every capture
-- length and both matches instantiate successfully. The template specialises
-- shared gaps and captures on unshared computed boxes to empty. Wire-only
-- overlaps use the computed interface at those empty capture lengths.
parameterPortOverlapTemplates
  :: (Traversable f, Eq (f ()), Eq (f a), Eq a)
  => (Int -> a) -> [Rule () (f a)] -> Either String [PortGraph () (f a)]
parameterPortOverlapTemplates fresh =
  portOverlapTemplatesBy "label parameters" parameterPortPattern ((==) `on` void) (solvePortLabels fresh)

portOverlapTemplatesBy
  :: (Eq l)
  => String
  -> (Rule () l -> Maybe (PortGraph () p))
  -> (p -> p -> Bool)
  -> ([(p, p)] -> [Either p p] -> Maybe [l])
  -> [Rule () l]
  -> Either String [PortGraph () l]
portOverlapTemplatesBy labelKind patternFor compatible solve rules = do
  patterns <- traverse validate rules
  pure
    [ source
    | first : rest <- tails patterns
    , (sameRule, second) <- (True, first) : map (False,) rest
    , source <- gluePortOverlap compatible solve sameRule first second
    ]
  where
    validate ruleToCheck = do
      left@(PortGraph sorts _ boxes) <-
        maybe
          (Left ("portOverlapTemplates: expected port rules with " ++ labelKind))
          Right
          (patternFor ruleToCheck)
      let lists = concatMap (\box -> [inputs box, outputs box]) boxes
          names = [name | ps <- lists, Capture name <- ps]
          used = IS.fromList [n | ps <- lists, Node n <- ps]
      unless
        (all oneCapturePerGap lists && length names == length (nubOrd names))
        (Left "portOverlapTemplates: captures must occur once, with at most one in each port-list gap")
      unless
        (IS.size used == length sorts)
        (Left "portOverlapTemplates: each numbered node must occur at a box port")
      replacement <-
        maybe
          (Left "portOverlapTemplates: expected a computed replacement or a fixed replacement without indexed captures")
          Right
          (overlapReplacement ruleToCheck)
      compiled <- compileRules [((), ruleToCheck)]
      pure (PortOverlapPattern left replacement compiled)
    oneCapturePerGap ps = not (any bothCaptures (zip ps (drop 1 ps)))
    bothCaptures (p, q) = isCapture p && isCapture q

data PortOverlapPattern p l = PortOverlapPattern (PortGraph () p) OverlapReplacement (CompiledRules () () l)

data OverlapReplacement = FixedInterface [Int] | MappedInterface [Int] | ComputedInterface (Maybe [Int])

gluePortOverlap
  :: (Eq l)
  => (p -> p -> Bool)
  -> ([(p, p)] -> [Either p p] -> Maybe [l])
  -> Bool
  -> PortOverlapPattern p l
  -> PortOverlapPattern p l
  -> [PortGraph () l]
gluePortOverlap
  compatible
  solve
  sameRule
  (PortOverlapPattern (PortGraph ls li left) leftReplacement leftCompiled)
  (PortOverlapPattern (PortGraph rs ri right) rightReplacement rightCompiled) = do
    boxPairs <-
      [[] | wireConflictPossible]
        ++ map (: []) candidates
        ++ [[p, q] | p@(i, j) : rest <- tails candidates, q@(k, l) <- rest, i /= k, j /= l]
    guard (not sameRule || boxPairs <= List.sort [(j, i) | (i, j) <- boxPairs])
    let leftOnly = IM.withoutKeys leftBoxes (IS.fromList (map fst boxPairs))
        rightOnly = IM.withoutKeys rightBoxes (IS.fromList (map snd boxPairs))
        attached side = IS.fromList [n | b <- IM.elems side, Node n <- inputs b ++ outputs b]
        outsideLeft = attached leftOnly
        outsideRight = attached rightOnly
        canIdentify l r =
          (IS.member l leftKept || IS.notMember r outsideRight)
            && (IS.member r rightKept || IS.notMember l outsideLeft)
    let sharedLabels = [(label (leftBoxes IM.! i), label (rightBoxes IM.! j)) | (i, j) <- boxPairs]
        sourceLabels = map (Left . label) left ++ map (Right . label) (IM.elems rightOnly)
    labels <- maybeToList (solve sharedLabels sourceLabels)
    shared <- IM.fromList <$> traverse (share canIdentify) boxPairs
    let sharedPorts = concatMap (\b -> inputs b ++ outputs b) (IM.elems shared)
        wirePairs = nubOrd [(r, l) | Identified l r <- sharedPorts]
        rightToLeft = IM.fromList wirePairs
        leftToRight = IM.fromList [(l, r) | (r, l) <- wirePairs]
        solo = [n | Unaligned (Node n) <- sharedPorts]
        -- A solo numbered port occurs inside the other rule's capture.
        -- Any numbered node identified with it must survive that rule.
        preservesCaptured n =
          maybe True (`IS.member` leftKept) (IM.lookup n rightToLeft)
            && maybe True (`IS.member` rightKept) (IM.lookup n leftToRight)
    guard (IM.size rightToLeft == length wirePairs && IM.size leftToRight == length wirePairs)
    guard (all preservesCaptured solo)
    extraPairs <-
      partialInjections
        [ (r, IS.toList (IS.difference leftKept (IM.keysSet leftToRight)))
        | r <- IS.toList (IS.difference rightKept (IM.keysSet rightToLeft))
        ]
    let wires = IM.union rightToLeft (IM.fromList extraPairs)
        identical =
          boxPairs == [(i, i) | i <- IM.keys leftBoxes]
            && null solo
            && all (\(r, l) -> r == length ls + l) (IM.toList wires)
    guard (not sameRule || not identical)
    guard
      ( not (null boxPairs)
          || sharesMergedWires (IS.fromList (IM.elems wires)) (IM.keysSet wires)
      )
    let canonical n = IM.findWithDefault n n wires
        retained = [(i, s) | (i, s) <- zip [0 ..] (ls ++ rs), IM.notMember i wires]
        indices = IM.fromList (zip (map fst retained) [0 ..])
        deleted = IS.fromList [canonical i | i <- [0 .. length ls + length rs - 1], IS.notMember i kept]
        boundary = [j | (i, j) <- IM.toList indices, IS.notMember i deleted]
        kept = IS.union leftKept rightKept
        resolve (Identified l _) = Node (indices IM.! l)
        resolve (Unaligned (Node n)) = Node (indices IM.! canonical n)
        resolve (Unaligned p) = p
        boxes =
          IM.elems (IM.union shared (fmap (unsharedBox leftReplacement) leftOnly))
            ++ IM.elems (fmap (unsharedBox rightReplacement) rightOnly)
        source = PortGraph (map snd retained) boundary [Box l (map resolve i) (map resolve o) | (l, Box _ i o) <- zip labels boxes]
    unless bothFixed do
      host <- either (const []) pure (symbolicPortGraph source)
      let Graph _ markerBoundary _ _ = host
          protected = IS.fromList (drop (length boundary) markerBoundary)
          leftSelection = IM.keysSet leftBoxes
          rightSelection = IS.fromList (map fst boxPairs ++ [length left .. length boxes - 1])
          matchesUsing selection compiled =
            [ prepared
            | (_, (prepared@(_, _, (_, selected)), _)) <- compiledMatchesWithMaps protected compiled host
            , selected == selection
            ]
          leftMatches = matchesUsing leftSelection leftCompiled
          rightMatches = matchesUsing rightSelection rightCompiled
          sharedNodes = IS.fromList [indices IM.! l | l <- IM.elems wires]
          mergesShared (Graph _ lhsInterface _ _, Graph _ rhsInterface _ _, (images, _)) =
            identifiesNodes (zip (map (images IM.!) lhsInterface) rhsInterface) sharedNodes
      if sameRule && leftSelection == rightSelection
        then guard (length leftMatches >= 2)
        else guard (not (null leftMatches) && not (null rightMatches))
      guard (not (null boxPairs) || any mergesShared leftMatches || any mergesShared rightMatches)
    pure source
    where
      bothFixed = case (leftReplacement, rightReplacement) of
        (FixedInterface _, FixedInterface _) -> True
        _ -> False
      keepSharedGaps = supportsMarkers leftReplacement && supportsMarkers rightReplacement
      supportsMarkers ComputedInterface{} = False
      supportsMarkers _ = True
      leftKept = IS.fromList li
      rightInterface = map (+ length ls) ri
      rightKept = IS.fromList rightInterface
      wireConflictPossible = sharesMergedWires leftKept rightKept
      sharesMergedWires leftShared rightShared
        | IS.size leftShared < 2 || IS.size rightShared < 2 = False
        | otherwise = case (wireOnlyInterface leftReplacement, wireOnlyInterface rightReplacement) of
            (Just lt, Just rt) ->
              identifiesNodes (zip li lt) leftShared || identifiesNodes (zip rightInterface rt) rightShared
            _ -> False
      wireOnlyInterface (FixedInterface targets) = Just targets
      wireOnlyInterface (MappedInterface targets) = Just targets
      wireOnlyInterface (ComputedInterface targets) = targets
      unsharedBox (ComputedInterface _) (Box l ins outs) =
        let known = map Unaligned . filter (not . isCapture)
        in Box l (known ins) (known outs)
      unsharedBox _ box = fmap Unaligned box
      leftBoxes = indexed (rename "left:" 0) left
      rightBoxes = indexed (rename "right:" (length ls)) right
      indexed f = IM.fromDistinctAscList . zip [0 ..] . map (fmap f)
      candidates = [(i, j) | (i, l) <- IM.toList leftBoxes, (j, r) <- IM.toList rightBoxes, compatible (label l) (label r)]
      share canIdentify (i, j) = do
        let l = leftBoxes IM.! i
            r = rightBoxes IM.! j
            prefix = "shared:" ++ show i ++ ":"
        ins <- alignPortLists keepSharedGaps canIdentify (prefix ++ "inputs:") (inputs l) (inputs r)
        outs <- alignPortLists keepSharedGaps canIdentify (prefix ++ "outputs:") (outputs l) (outputs r)
        pure (i, Box (label l) ins outs)
      rename _ offset (Node n) = Node (offset + n)
      rename prefix _ (Capture name) = Capture (prefix ++ name)
      rename prefix _ (Element name i) = Element (prefix ++ name) i

data AlignedPort = Unaligned Port | Identified Int Int

-- A side can take a numbered port from the other side only while its current
-- gap is open. Taking both ports identifies their nodes in the overlap.
alignPortLists :: Bool -> (Int -> Int -> Bool) -> String -> [Port] -> [Port] -> [[AlignedPort]]
alignPortLists keepSharedGaps canIdentify prefix = go (0 :: Int)
  where
    go i left right = map (common ++) continuations
      where
        (leftOpen, ls) = gap left
        (rightOpen, rs) = gap right
        common = [Unaligned (Capture (prefix ++ show i)) | keepSharedGaps && leftOpen && rightOpen]
        continuations = case (ls, rs) of
          ([], []) -> [[]]
          _ ->
            [Unaligned p : rest | rightOpen, p : ps <- [ls], rest <- go (i + 1) ps right]
              ++ [Unaligned p : rest | leftOpen, p : ps <- [rs], rest <- go (i + 1) left ps]
              ++ [Identified l r : rest | Node l : ps <- [ls], Node r : qs <- [rs], canIdentify l r, rest <- go (i + 1) ps qs]
    gap (Capture _ : ps) = (True, ps)
    gap ps = (False, ps)

isCapture :: Port -> Bool
isCapture Capture{} = True
isCapture _ = False

literalPortPattern :: Rule s l -> Maybe (PortGraph s l)
literalPortPattern (PortRule (PortGraph sorts boundary lhs) PortTemplate{}) =
  PortGraph sorts boundary <$> traverse literalBox lhs
  where
    literalBox (Box (ExactLabel l) i o) = Just (Box l i o)
    literalBox (Box ConstructorLabel{} _ _) = Nothing
literalPortPattern _ = Nothing

parameterPortPattern :: Rule s (f a) -> Maybe (PortGraph s (f (Parameter a)))
parameterPortPattern (PortRule (PortGraph sorts boundary lhs) replacement) = do
  parameters <- case replacement of
    ParameterPorts ps _ -> Just ps
    ComputedPorts ps _ -> Just ps
    MappedPorts ps _ _ -> Just ps
    PortTemplate{} -> Nothing
  pure (PortGraph sorts boundary [Box l i o | (l, Box _ i o) <- zip parameters lhs])
parameterPortPattern _ = Nothing

data ScopedParameter a = ScopedVariable (Either String String) | ScopedLiteral a

solvePortLabels
  :: (Traversable f, Eq a)
  => (Int -> a)
  -> [(f (Parameter a), f (Parameter a))]
  -> [Either (f (Parameter a)) (f (Parameter a))]
  -> Maybe [f a]
solvePortLabels fresh shared sources = do
  boxes <- traverse (either (traverse (scope Left)) (traverse (scope Right))) sources
  equations <- concat <$> traverse fields shared
  let variables =
        nubOrd [n | ScopedVariable n <- concatMap toList boxes ++ concat [[l, r] | (l, r) <- equations]]
      ids = M.fromList (zip variables [0 ..])
      root = unionFind [(ids M.! l, ids M.! r) | (ScopedVariable l, ScopedVariable r) <- equations]
      representative n = root (ids M.! n)
      bind acc (ScopedLiteral l, ScopedLiteral r) = acc <$ guard (l == r)
      bind acc (ScopedVariable n, ScopedLiteral a) = assign acc (representative n) a
      bind acc (ScopedLiteral a, ScopedVariable n) = assign acc (representative n) a
      bind acc (ScopedVariable _, ScopedVariable _) = Just acc
  literals <- foldM bind IM.empty equations
  let instantiate (ScopedLiteral a) = a
      instantiate (ScopedVariable n) =
        let i = representative n in IM.findWithDefault (fresh i) i literals
  pure (map (fmap instantiate) boxes)
  where
    scope _ (Literal a) = Just (ScopedLiteral a)
    scope side (Variable n) = Just (ScopedVariable (side n))
    scope _ _ = Nothing
    fields (l, r) = zip <$> traverse (scope Left) (toList l) <*> traverse (scope Right) (toList r)
    assign literals i a = case IM.lookup i literals of
      Nothing -> Just (IM.insert i a literals)
      Just b -> literals <$ guard (a == b)

overlapReplacement :: Rule s l -> Maybe OverlapReplacement
overlapReplacement (PortRule lhs replacement) = case replacement of
  PortTemplate rhs -> FixedInterface <$> interfaceWithoutElements rhs
  ParameterPorts _ rhs -> FixedInterface <$> interfaceWithoutElements rhs
  ComputedPorts _ build ->
    -- An indexed element cannot exist in an empty capture.
    let emptyLengths = M.fromList [(name, 0) | name <- portSequenceNames lhs]
    in Just (ComputedInterface (build emptyLengths >>= interfaceWithoutElements))
  MappedPorts _ rhs _ -> MappedInterface <$> interfaceWithoutElements rhs
  where
    interfaceWithoutElements (PortGraph _ boundary rhs) =
      boundary <$ guard (all supported [p | box <- rhs, p <- inputs box ++ outputs box])
    supported Element{} = False
    supported _ = True
overlapReplacement _ = Nothing

symbolicPortGraph :: PortGraph () l -> Either String (Graph () l)
symbolicPortGraph template@(PortGraph sorts boundary boxes) = do
  checkPortLeft template
  let names = portSequenceNames template
      markers = take (length names) [length sorts ..]
      positions = M.fromList (zip names markers)
      resolve (Node i) = Right i
      resolve (Capture name) = Right (positions M.! name)
      resolve Element{} = Left "checkPortTemplate: Element in the source"
      expand (Box l ins outs) = Box l <$> traverse resolve ins <*> traverse resolve outs
  Graph (sorts ++ replicate (length names) (Some @'())) (boundary ++ markers) [] <$> traverse expand boxes

portSequenceNames :: PortGraph s l -> [String]
portSequenceNames (PortGraph _ _ boxes) = nubOrd [name | box <- boxes, Capture name <- inputs box ++ outputs box]

restorePortSequences :: Int -> [String] -> Graph () l -> Either String (PortGraph () l)
restorePortSequences boundarySize names (Graph sorts ins outs boxes) = do
  unless (null outs && length markers == length names && IM.size captures == length names) invalidBoundary
  interface <- traverse reindex boundary
  restored <- traverse (\(Box l i o) -> Box l <$> traverse restore i <*> traverse restore o) boxes
  pure (PortGraph (map snd numbered) interface restored)
  where
    invalidBoundary = Left "orientPortOverlap: the witness changed a sequence marker at the boundary"
    (boundary, markers) = splitAt boundarySize ins
    captures = IM.fromList (zip markers names)
    numbered = [(i, sort) | (i, sort) <- zip [0 ..] sorts, IM.notMember i captures]
    indices = IM.fromList (zip (map fst numbered) [0 ..])
    reindex i = maybe invalidBoundary Right (IM.lookup i indices)
    restore i = maybe (Node <$> reindex i) (Right . Capture) (IM.lookup i captures)

literalRule :: (key, Rule s l) -> Either String (FixedRule key s l)
literalRule (key, Rule patternGraph instantiate) = do
  lhs@(Graph _ _ _ bs) <-
    maybe (Left "expected literal labels") Right (traverseLabels exact patternGraph)
  rhs <- maybe (Left "the rule rejected its own pattern") Right (instantiate (map label bs))
  pure (key, lhs, rhs)
  where
    exact :: LabelTest l -> Maybe l
    exact (ExactLabel l) = Just l
    exact ConstructorLabel{} = Nothing
literalRule _ = Left "expected a fixed rule"

fixedRule :: (key, Rule s l) -> Either String (FixedRule key s l)
fixedRule ruleEntry = do
  fixed@(_, lhs, rhs) <- literalRule ruleEntry
  unless
    (validDiagram lhs && validDiagram rhs)
    (Left "rule sides must be monogamous acyclic diagrams")
  pure fixed

-- | Inspect the parallel sides of a fixed string-diagram rule. Both sides
-- must have monogamous acyclic wiring, as in 'compileConvexRules'.
withFixedRule
  :: forall s l r
   . Rule s l
  -> (forall as bs. (Wires @s @l as ~> Wires @s @l bs) -> (Wires @s @l as ~> Wires @s @l bs) -> r)
  -> Either String r
withFixedRule fixed inspect = do
  (_, lhs, rhs) <- fixedRule ((), fixed)
  pure (withDiagramBoundary lhs (\makeDiagram -> inspect (makeDiagram lhs) (makeDiagram rhs)))

validDiagram :: Graph s l -> Bool
validDiagram (Graph ns ins outs bs) =
  diagramBoundary (length ns) bs == Just (List.sort ins, List.sort outs)

diagramBoundary :: Int -> [Box l Int] -> Maybe ([Int], [Int])
diagramBoundary n bs = do
  guard (length produced == IS.size producers && length consumed == IS.size consumers)
  guard (all acyclic (stronglyConnComp [(v, v, IM.findWithDefault [] v edges) | v <- vertices]))
  pure ([v | v <- vertices, IS.notMember v producers], [v | v <- vertices, IS.notMember v consumers])
  where
    vertices = [0 .. n - 1]
    produced = concatMap outputs bs
    consumed = concatMap inputs bs
    producers = IS.fromList produced
    consumers = IS.fromList consumed
    edges = wireEdges bs
    acyclic AcyclicSCC{} = True
    acyclic CyclicSCC{} = False

wireEdges :: [Box l Int] -> IM.IntMap [Int]
wireEdges bs = IM.fromListWith (++) [(i, outputs b) | b <- bs, i <- inputs b]

reachableNodes :: IM.IntMap [Int] -> Int -> IS.IntSet
reachableNodes edges start = visit IS.empty [start]
  where
    visit seen [] = seen
    visit seen (i : rest)
      | IS.member i seen = visit seen rest
      | otherwise = visit (IS.insert i seen) (IM.findWithDefault [] i edges ++ rest)

type FixedRule :: Type -> Kind -> Type -> Type
type FixedRule key s l = (key, Graph s l, Graph s l)

type DiagramStep :: Type -> Kind -> Type -> Type
type DiagramStep key s l = (key, Graph s l, Graph s l, Match)

type PreCriticalPair :: Type -> Kind -> Type -> Type
type PreCriticalPair key s l = (Graph s l, DiagramStep key s l, DiagramStep key s l)

data OverlapMode = StringOverlaps Bool | HypergraphOverlaps

preCriticalPairs
  :: (Eq l, DecidableIso s)
  => OverlapMode -> [FixedRule key s l] -> [PreCriticalPair key s l]
preCriticalPairs mode patterns =
  [ peak
  | (first : rest) <- tails patterns
  , (sameRule, second) <- (True, first) : map (False,) rest
  , peak <- glueOverlaps mode sameRule first second
  ]

glueOverlaps
  :: (Eq l, DecidableIso s)
  => OverlapMode -> Bool -> FixedRule key s l -> FixedRule key s l -> [PreCriticalPair key s l]
glueOverlaps mode sameRule (lk, left@(Graph ls li lo lb), lr) (rk, right@(Graph rs ri ro rb), rr) = do
  boxPairs <-
    partialInjections
      [(j, [i | (i, l) <- zip [0 ..] lb, compatible l r]) | (j, r) <- zip [0 ..] rb]
  case mode of
    StringOverlaps includeParallel -> guard (includeParallel || not (null boxPairs))
    HypergraphOverlaps -> guard (not (null boxPairs) || interferesOnWires left lr right || interferesOnWires right rr left)
  let ports =
        concat
          [zip (inputs r ++ outputs r) (inputs l ++ outputs l) | (j, i) <- boxPairs, let r = rb !! j, let l = lb !! i]
  (forced, used) <- maybeToList (foldM bind (IM.empty, IS.empty) ports)
  -- Sharing a box identifies its ports. Monogamous wiring only allows further
  -- identifications between an unused input and an unused output.
  let nodeCandidates = case mode of
        StringOverlaps _ -> [(ri, lo), (ro, li)]
        HypergraphOverlaps -> [([0 .. length rs - 1], [0 .. length ls - 1])]
  wirePairs <-
    partialInjections
      [ (j, [i | i <- candidates, IS.notMember i used, sameSort (rs !! j) (ls !! i)])
      | (boundary, candidates) <- nodeCandidates
      , j <- boundary
      , IM.notMember j forced
      ]
  let shared = IM.union forced (IM.fromList wirePairs)
      inverse pairs = List.sort [(b, a) | (a, b) <- pairs]
      wires = IM.toList shared
  guard (not sameRule || (List.sort boxPairs, wires) <= (inverse boxPairs, inverse wires))
  let fresh = [(j, s) | (j, s) <- zip [0 ..] rs, IM.notMember j shared]
      ns = ls ++ map snd fresh
      nodeMap = IM.union shared (IM.fromList (zip (map fst fresh) [length ls ..]))
      sharedBoxes = IM.fromList boxPairs
      remaining = [(j, b) | (j, b) <- zip [0 ..] rb, IM.notMember j sharedBoxes]
      boxMap = IM.union sharedBoxes (IM.fromList (zip (map fst remaining) [length lb ..]))
      bs = lb ++ [fmap (nodeMap IM.!) b | (_, b) <- remaining]
      lm = (IM.fromList [(i, i) | i <- [0 .. length ls - 1]], IS.fromList [0 .. length lb - 1])
      rm = (nodeMap, IS.fromList (IM.elems boxMap))
  guard (not sameRule || lm /= rm)
  (ins, outs) <- case mode of
    StringOverlaps _ -> maybeToList (diagramBoundary (length ns) bs)
    HypergraphOverlaps -> do
      let leftDeleted = deletedImages left (fst lm)
          rightDeleted = deletedImages right (fst rm)
      guard
        ( length (nonConflictingBy const [(leftDeleted, lm), (rightDeleted, rm)])
            == 1
              || identifiesMatchNodes left lr lm rm
              || identifiesMatchNodes right rr rm lm
        )
      let deleted = IS.union leftDeleted rightDeleted
      pure ([i | i <- [0 .. length ns - 1], IS.notMember i deleted], [])
  let host = Graph ns ins outs bs
  guard (lm `elem` map fst (matches lhs host) && rm `elem` map fst (matches rhs host))
  pure (host, (lk, left, lr, lm), (rk, right, rr, rm))
  where
    lhs = mapLabels ExactLabel left
    rhs = mapLabels ExactLabel right
    compatible (Box l i o) (Box r j p) = l == r && length i == length j && length o == length p
    bind (mapping, used) (j, i)
      | Just previous <- IM.lookup j mapping = (mapping, used) <$ guard (previous == i)
      | IS.member i used || not (sameSort (rs !! j) (ls !! i)) = Nothing
      | otherwise = Just (IM.insert j i mapping, IS.insert i used)

-- Disjoint boxes can interfere through node deletion or identification.
interferesOnWires :: (DecidableIso s) => Graph s l -> Graph s l -> Graph s l -> Bool
interferesOnWires lhs@(Graph sorts li lo _) (Graph _ ri ro _) (Graph otherSorts _ _ _) =
  any canDelete (internalNodes lhs)
    || (length targets /= IS.size (IS.fromList targets) && any canMerge (IM.elems mergedSources))
  where
    targets = ri ++ ro
    mergedSources = IM.fromListWith (++) [(r, [l]) | (l, r) <- zip (li ++ lo) targets]
    canDelete node = any (sameSort (sorts !! node)) otherSorts
    -- A merge identifies two nodes of the same sort in the other match.
    canMerge (node : _ : _) = case filter (sameSort (sorts !! node)) otherSorts of
      _ : _ : _ -> True
      _ -> False
    canMerge _ = False

-- A replacement can identify nodes that another match needs to keep distinct.
identifiesMatchNodes :: Graph s l -> Graph s l -> Match -> Match -> Bool
identifiesMatchNodes (Graph _ li lo _) (Graph _ ri ro _) (mapping, _) (other, _) =
  identifiesNodes (zip (map (mapping IM.!) (li ++ lo)) (ri ++ ro)) (IS.fromList (IM.elems other))

identifiesNodes :: [(Int, Int)] -> IS.IntSet -> Bool
identifiesNodes interface readNodes =
  length targets /= IS.size (IS.fromList targets)
  where
    targets = [r | (l, r) <- interface, IS.member l readNodes]

partialInjections :: [(Int, [Int])] -> [[(Int, Int)]]
partialInjections = go IS.empty
  where
    go _ [] = [[]]
    go used ((i, choices) : rest) =
      go used rest
        ++ [(i, j) : pairs | j <- choices, IS.notMember j used, pairs <- go (IS.insert j used) rest]

renderOverlap :: forall key s l. Graph s l -> DiagramStep key s l -> DiagramStep key s l -> CriticalOverlap key s l
renderOverlap host left@(lk, _, _, _) right@(rk, _, _, _) =
  withDiagramBoundary host \toDiagram ->
    CriticalOverlap lk rk (toDiagram host) (toDiagram (applyStep host left)) (toDiagram (applyStep host right))

withDiagramBoundary
  :: forall s l r
   . Graph s l
  -> (forall as bs. (Graph s l -> Wires @s @l as ~> Wires @s @l bs) -> r)
  -> r
withDiagramBoundary (Graph ns ins outs _) k =
  reifySorts (map (ns !!) ins) \ @as -> reifySorts (map (ns !!) outs) \ @bs ->
    let toDiagram :: Graph s l -> (Wires as :: OPENHG s l) ~> Wires bs
        toDiagram (Graph ss is os boxes) = unsafeOpenHypergraph ss is os boxes
    in k toDiagram

applyStep :: Graph s l -> DiagramStep key s l -> Graph s l
applyStep host (_, lhs, rhs, match) = replaceMany lhs rhs host [match]

-- | The result of testing all maximal path contexts. A failed join contains
-- its extended source and both reducts. 'Left' labels in that witness are
-- the numbered formal path boxes, and 'Right' labels are original generators.
-- Failure concerns the extended signature that includes the formal boxes.
type PathContextResult :: Type -> Kind -> Type -> Type
data PathContextResult key s l
  = PathContextsJoinable Int
  | PathContextNotJoinable (CriticalOverlap key s (Either Int l))
  | PathContextLimitReached

-- | Check path joinability for fixed, left-linear string-diagram rules.
-- Includes parallel pairs, which can interfere under convex matching. Both
-- sides of each rule must be monogamous and acyclic. The optional bound is
-- the maximum search depth from each reduct, for each path context. Use
-- 'Nothing' for a terminating rule set to exhaust the search.
-- See <https://arxiv.org/html/2109.06049#S5.SS5 String Diagram Rewrite Theory III, §5.5>.
checkPathContexts
  :: (Eq l, DecidableIso s)
  => Maybe Natural -> [(key, Rule s l)] -> Either String (PathContextResult key s l)
checkPathContexts maxDepth rules = do
  patterns <- traverse fixedRule rules
  pure $ case checkContexts maxDepth patterns (preCriticalPairs (StringOverlaps True) patterns) of
    AllJoinable count -> PathContextsJoinable count
    Unjoinable (host, left, right) -> PathContextNotJoinable (renderOverlap host left right)
    JoinLimit _ -> PathContextLimitReached

checkContexts
  :: (Eq l, DecidableIso s)
  => Maybe Natural -> [FixedRule key s l] -> [PreCriticalPair key s l] -> PairCheck key s (Either Int l)
checkContexts maxDepth patterns = checkPairs maxDepth (convexReducts (convexRulesWith Right patterns)) . pathContexts

pathContexts :: [PreCriticalPair key s l] -> [PreCriticalPair key s (Either Int l)]
pathContexts pairs =
  [ (pathExtension host relation, liftStep first, liftStep second)
  | (host, first, second) <- pairs
  , relation <- maximalPathRelations host (forbiddenPaths first ++ forbiddenPaths second)
  ]

liftStep :: DiagramStep key s l -> DiagramStep key s (Either Int l)
liftStep (key, lhs, rhs, match) = (key, mapLabels Right lhs, mapLabels Right rhs, match)

type PairCheck key s l = JoinCheck (PreCriticalPair key s l)

data JoinCheck a
  = AllJoinable Int
  | Unjoinable a
  | JoinLimit a

checkPairs
  :: (Eq l, DecidableIso s)
  => Maybe Natural -> (Graph s l -> [Graph s l]) -> [PreCriticalPair key s l] -> PairCheck key s l
checkPairs maxDepth reducts = checkJoins (joinGraphs maxDepth reducts) \(host, left, right) -> (applyStep host left, applyStep host right)

checkJoins :: (g -> g -> Maybe Bool) -> (a -> (g, g)) -> [a] -> JoinCheck a
checkJoins join branches = checkAll 0 Nothing
  where
    checkAll count pending [] = maybe (AllJoinable count) JoinLimit pending
    checkAll count pending (pair : more) =
      case uncurry join (branches pair) of
        Just True -> checkAll (count + 1) pending more
        Just False -> Unjoinable pair
        Nothing -> checkAll count (Just (fromMaybe pair pending)) more

checkHypergraphPairs
  :: (Eq l, DecidableIso s)
  => Maybe Natural -> (Graph s l -> [Prepared s l]) -> [FixedRule key s l] -> PairCheck key s l
checkHypergraphPairs maxDepth next = checkPairs maxDepth (singleReducts next) . preCriticalPairs HypergraphOverlaps

-- | The rules returned by bounded convex completion. Supplied rules come
-- before learned rules. On success, redundant rules may be removed and
-- retained right sides may be simplified. All path contexts of the resulting
-- system rejoin.
type ConvexCompletion :: Kind -> Type -> Type
data ConvexCompletion s l
  = ConvexComplete [Rule s l] (ConvexRules s l)
  | ConvexIncomplete [Rule s l] (ConvexCompletionStop s l)

-- | Why completion stopped. Rule keys in witnesses are zero-based positions
-- in the returned rule list. 'Left' labels denote formal path boxes.
type ConvexCompletionStop :: Kind -> Type -> Type
data ConvexCompletionStop s l
  = ConvexRuleLimit (CriticalOverlap Int s l)
  | ConvexJoinLimit (CriticalOverlap Int s (Either Int l))
  | ConvexUnorientable String (CriticalOverlap Int s l)
  | ConvexContextFailure (CriticalOverlap Int s (Either Int l))

-- | Knuth–Bendix-style completion of a fixed string-diagram presentation,
-- bounded by the number of new rules and the search depth from each reduct.
-- On a failed join in the empty context, orient the two deterministic normal
-- forms using the supplied comparison. The caller supplies a well-founded order invariant
-- under isomorphism and preserved by contexts, and ensures the initial rules
-- decrease in that order.
-- Failures in formal path contexts are returned with their witnesses.
-- After success, use the other rules to remove redundant rules and simplify
-- right sides. Keep each change only when the resulting system passes the
-- path-context check within the same depth bound.
completeConvex
  :: forall s l
   . (Eq l, DecidableIso s)
  => Natural
  -> Natural
  -> (forall as bs. (Wires @s @l as ~> Wires @s @l bs) -> (Wires @s @l as ~> Wires @s @l bs) -> Ordering)
  -> [Rule s l]
  -> Either String (ConvexCompletion s l)
completeConvex maxRules maxDepth compareDiagrams initial = do
  patterns <- traverse fixedRule (zip [0 ..] initial)
  pure (go maxRules initial patterns)
  where
    go budget rules patterns =
      let compiled = convexRulesWith id patterns
          pairs = preCriticalPairs (StringOverlaps True) patterns
          bare =
            [ pair
            | pair@(Graph _ _ _ boxes, left, right) <- pairs
            , let edges = wireEdges boxes
            , all (\(o, i) -> IS.notMember i (reachableNodes edges o)) (forbiddenPaths left ++ forbiddenPaths right)
            ]
          incomplete = ConvexIncomplete rules
          withMarkers (host, left, right) = renderOverlap (mapLabels Right host) (liftStep left) (liftStep right)
      in case checkPairs (Just maxDepth) (convexReducts compiled) bare of
           Unjoinable (host, left, right) ->
             let peak = renderOverlap host left right
             in if budget == 0
                  then incomplete (ConvexRuleLimit peak)
                  else case orientPeak maxDepth compareDiagrams (convexMatches compiled) rule peak of
                    Left err -> incomplete (ConvexUnorientable err peak)
                    Right newRule -> case fixedRule (length rules, newRule) of
                      Left err -> incomplete (ConvexUnorientable err peak)
                      Right pattern' -> go (budget - 1) (rules ++ [newRule]) (patterns ++ [pattern'])
           JoinLimit pair -> incomplete (ConvexJoinLimit (withMarkers pair))
           AllJoinable _ ->
             case checkContexts (Just maxDepth) patterns pairs of
               AllJoinable _ ->
                 let next = convexMatches . convexRulesWith id
                     check ps = checkContexts (Just maxDepth) ps (preCriticalPairs (StringOverlaps True) ps)
                     (remainingRules, remainingPatterns) = unzip (interreduce maxDepth next check (zip rules patterns))
                 in ConvexComplete remainingRules (convexRulesWith id remainingPatterns)
               JoinLimit (host, left, right) -> incomplete (ConvexJoinLimit (renderOverlap host left right))
               Unjoinable (host, left, right) -> incomplete (ConvexContextFailure (renderOverlap host left right))

-- | The result of checking and completing the overlaps enumerated by
-- 'hypergraphOverlaps'. The rules are listed in input and discovery order,
-- with redundant rules removed and right sides simplified on success.
type HypergraphCompletion :: Kind -> Type -> Type
data HypergraphCompletion s l
  = HypergraphComplete [Rule s l] (CompiledRules Int s l)
  | HypergraphIncomplete [Rule s l] (HypergraphCompletionStop s l)

-- | The outstanding overlap when bounded hypergraph completion stops. Rule
-- keys are zero-based positions in the returned rule list.
type HypergraphCompletionStop :: Kind -> Type -> Type
data HypergraphCompletionStop s l
  = HypergraphRuleLimit (CriticalOverlap Int s l)
  | HypergraphJoinLimit (CriticalOverlap Int s l)
  | HypergraphUnorientable String (CriticalOverlap Int s l)

-- | Bounded Knuth–Bendix-style completion of fixed literal hypergraph rules.
-- The two bounds limit the number of learned rules and the search depth from
-- each reduct. As with 'completeConvex', the caller supplies a well-founded
-- comparison that decreases on rules and is preserved by contexts.
-- Success establishes local confluence for the resulting single-step system
-- by the same check as 'checkHypergraphConfluence'. After a successful join
-- check, remove redundant rules and simplify right sides using the other
-- rules. Each change must pass the overlap check within the same depth bound.
-- A learned rule with repeated left boundary nodes uses one port per shared
-- node when both sides identify the same ports and the factored rule still
-- decreases. Otherwise completion returns 'HypergraphUnorientable' with the
-- original overlap witness.
completeHypergraph
  :: forall s l
   . (Eq l, DecidableIso s)
  => Natural
  -> Natural
  -> (forall as bs. (Wires @s @l as ~> Wires @s @l bs) -> (Wires @s @l as ~> Wires @s @l bs) -> Ordering)
  -> [Rule s l]
  -> Either String (HypergraphCompletion s l)
completeHypergraph maxRules maxDepth compareDiagrams initial = do
  patterns <- traverse literalRule (zip [0 ..] initial)
  go maxRules initial patterns
  where
    go budget rules patterns = do
      compiled <- compileRules (zip [0 :: Int ..] rules)
      let next = map snd . compiledMatches compiled
          incomplete = Right . HypergraphIncomplete rules
      case checkHypergraphPairs (Just maxDepth) next patterns of
        AllJoinable _ -> do
          let rewritesFor = fixedMatches . fixedPatterns id
              check ps = checkHypergraphPairs (Just maxDepth) (rewritesFor ps) ps
              retained = map fst (interreduce maxDepth rewritesFor check (zip rules patterns))
          HypergraphComplete retained <$> compileRules (zip [0 ..] retained)
        JoinLimit (host, left, right) -> incomplete (HypergraphJoinLimit (renderOverlap host left right))
        Unjoinable (host, left, right) ->
          let peak = renderOverlap host left right
          in if budget == 0
               then incomplete (HypergraphRuleLimit peak)
               else case orientPeak maxDepth compareDiagrams next (factorBoundaryRule compareDiagrams) peak of
                 Left err -> incomplete (HypergraphUnorientable err peak)
                 Right newRule -> do
                   pattern' <- literalRule (length rules, newRule)
                   go (budget - 1) (rules ++ [newRule]) (patterns ++ [pattern'])

factorBoundaryRule
  :: (forall as bs. Wires @s @l as ~> Wires @s @l bs -> Wires @s @l as ~> Wires @s @l bs -> Ordering)
  -> (a :: OPENHG s l) ~> b
  -> a ~> b
  -> Either String (Rule s l)
factorBoundaryRule compareDiagrams lhs rhs
  | length leftPorts == leftCount = rule lhs rhs
  | length pairs /= leftCount || length pairs /= IS.size (IS.fromList rightPorts) =
      Left "completion: the reducts identify different boundary ports"
  | otherwise = withDiagramBoundary left' \render ->
      let l = render left'
          r = render right'
      in if compareDiagrams l r == GT
           then rule l r
           else Left "completion: the factored rule does not decrease"
  where
    Graph ls li lo lb = graph lhs
    Graph rs ri ro rb = graph rhs
    leftPorts = li ++ lo
    rightPorts = ri ++ ro
    leftCount = IS.size (IS.fromList leftPorts)
    pairs = nubOrd (zip leftPorts rightPorts)
    (ins, outs) = splitAt (length (nubOrd li)) pairs
    left' = Graph ls (map fst ins) (map fst outs) lb
    right' = Graph rs (map snd ins) (map snd outs) rb

orientPeak
  :: Natural
  -> (forall as bs. (Wires @s @l as ~> Wires @s @l bs) -> (Wires @s @l as ~> Wires @s @l bs) -> Ordering)
  -> (Graph s l -> [Prepared s l])
  -> (forall as bs. (Wires @s @l as ~> Wires @s @l bs) -> (Wires @s @l as ~> Wires @s @l bs) -> Either String (Rule s l))
  -> CriticalOverlap key s l
  -> Either String (Rule s l)
orientPeak maxDepth compareDiagrams next makeRule (CriticalOverlap _ _ _ left right) =
  let limits = RewriteLimits (Just maxDepth) Nothing
      l = normaliseBy limits (take 1 . next) left
      r = normaliseBy limits (take 1 . next) right
      ln = normalisedGraph l
      rn = normalisedGraph r
  in if normalisationStatus l /= NormalForm || normalisationStatus r /= NormalForm
       then Left "could not normalise both reducts within the depth limit"
       else case compareDiagrams ln rn of
         LT -> makeRule rn ln
         GT -> makeRule ln rn
         EQ -> Left "the comparison did not orient the equation"

type RuleEntry key s l = (Rule s l, FixedRule key s l)

interreduce
  :: (Eq l, DecidableIso s)
  => Natural
  -> ([FixedRule key s l] -> Graph s l -> [Prepared s l])
  -> ([FixedRule key s l] -> PairCheck key s m)
  -> [RuleEntry key s l]
  -> [RuleEntry key s l]
interreduce depth next check = simplifyRightSides [] . pruneRules []
  where
    bound = Just depth
    pruneRules kept [] = reverse kept
    pruneRules kept (candidate@(_, (_, lhs, rhs)) : pending)
      | Just True <- joinGraphs bound (singleReducts (next patterns)) lhs rhs
      , AllJoinable _ <- check patterns =
          pruneRules [] remaining
      | otherwise = pruneRules (candidate : kept) pending
      where
        remaining = reverse kept ++ pending
        patterns = map snd remaining

    simplifyRightSides kept [] = reverse kept
    simplifyRightSides kept (candidate@(_, (key, lhs, rhs)) : pending) =
      simplifyRightSides (chosen : kept) pending
      where
        before = map snd (reverse kept)
        after = map snd pending
        result = normaliseGraphBy (RewriteLimits bound Nothing) (take 1 . next (before ++ after)) rhs
        reduced = normalisedGraph result
        replacement = (key, lhs, reduced)
        patterns = before ++ replacement : after
        chosen
          | normalisationStatus result == NormalForm
          , normalisationRewrites result > 0
          , AllJoinable _ <- check patterns =
              (Rule (mapLabels ExactLabel lhs) (const (Just reduced)), replacement)
          | otherwise = candidate

-- In a monogamous acyclic diagram, a path can leave and re-enter a match
-- only through an output and an input of its left side.
forbiddenPaths :: DiagramStep key s l -> [(Int, Int)]
forbiddenPaths (_, Graph _ ins outs _, _, (mapping, _)) =
  [(mapping IM.! o, mapping IM.! i) | o <- outs, i <- ins]

-- | Validated fixed rules for convex string-diagram rewriting.
type ConvexRules :: Kind -> Type -> Type
newtype ConvexRules s l = ConvexRules [(Graph s (LabelTest l), Graph s l)]

-- | Validate fixed rules with monogamous acyclic sides. Rule order determines
-- which match 'normaliseConvex' takes when several are available.
compileConvexRules :: [Rule s l] -> Either String (ConvexRules s l)
compileConvexRules rules = convexRulesWith id <$> traverse (fixedRule . ((),)) rules

convexRulesWith :: (l -> m) -> [FixedRule key s l] -> ConvexRules s m
convexRulesWith wrap = ConvexRules . fixedPatterns wrap

fixedPatterns :: (l -> m) -> [FixedRule key s l] -> [(Graph s (LabelTest m), Graph s m)]
fixedPatterns wrap patterns =
  [(mapLabels (ExactLabel . wrap) lhs, mapLabels wrap rhs) | (_, lhs, rhs) <- patterns]

convexReducts :: (Eq l, DecidableIso s) => ConvexRules s l -> Graph s l -> [Graph s l]
convexReducts rules = singleReducts (convexMatches rules)

singleReducts :: (Graph s l -> [Prepared s l]) -> Graph s l -> [Graph s l]
singleReducts next host =
  [replaceMany lhs rhs host [match] | (lhs, rhs, match) <- next host]

convexMatches :: (Eq l, DecidableIso s) => ConvexRules s l -> Graph s l -> [Prepared s l]
convexMatches (ConvexRules rules) host@(Graph _ _ _ bs) =
  [ (lhs, rhs, match)
  | (lhs@(Graph _ ins outs _), rhs, match@(mapping, _)) <- fixedMatches rules host
  , all
      ( \o ->
          let reachable = reachableNodes edges (mapping IM.! o)
          in all (\i -> IS.notMember (mapping IM.! i) reachable) ins
      )
      outs
  ]
  where
    edges = wireEdges bs

fixedMatches
  :: (Eq l, DecidableIso s) => [(Graph s (LabelTest l), Graph s l)] -> Graph s l -> [Prepared s l]
fixedMatches rules host =
  [(lhs, rhs, match) | (lhs, rhs) <- rules, (match, _) <- matches lhs host]

-- Search by depth on both sides. A failed join requires exhausting both
-- descendant sets. The seen sets also make finite cyclic searches terminate.
joinGraphs
  :: (Eq l, DecidableIso s)
  => Maybe Natural -> (Graph s l -> [Graph s l]) -> Graph s l -> Graph s l -> Maybe Bool
joinGraphs = joinGraphsWith sameGraph

joinGraphsWith
  :: (Eq l, DecidableIso s)
  => (Graph s l -> Graph s l -> Bool)
  -> Maybe Natural
  -> (Graph s l -> [Graph s l])
  -> Graph s l
  -> Graph s l
  -> Maybe Bool
joinGraphsWith = joinGraphsBy sameGraph

joinGraphsBy :: (g -> g -> Bool) -> (g -> g -> Bool) -> Maybe Natural -> (g -> [g]) -> g -> g -> Maybe Bool
joinGraphsBy same equivalent maxDepth next left right = search maxDepth [] [left] [] [right]
  where
    search depth seenL frontL seenR frontR
      | any (\g -> any (equivalent g) (frontR ++ seenR)) frontL
          || any (\g -> any (equivalent g) seenL) frontR =
          Just True
      | null frontL && null frontR = Just False
      | otherwise =
          let (seenL', frontL') = advance seenL frontL
              (seenR', frontR') = advance seenR frontR
          in case depth of
               Just 0 -> if null frontL' && null frontR' then Just False else Nothing
               _ -> search (subtract 1 <$> depth) seenL' frontL' seenR' frontR'
    advance seen front = (seen', freshBy same seen' (concatMap next front))
      where
        seen' = front ++ seen

-- Search shallowest first, using match priority to break ties at each depth.
normalFormWithinBy :: (g -> g -> Bool) -> Natural -> (g -> [g]) -> g -> Maybe g
normalFormWithinBy same maxDepth next start = search maxDepth [] [start]
  where
    search _ _ [] = Nothing
    search depth seen front =
      let layer = [(g, next g) | g <- front]
          seen' = front ++ seen
      in case List.find (null . snd) layer of
           Just (g, _) -> Just g
           Nothing
             | depth == 0 -> Nothing
             | otherwise -> search (depth - 1) seen' (reverse (freshBy same seen' (concatMap snd layer)))

freshBy :: (g -> g -> Bool) -> [g] -> [g] -> [g]
freshBy same seen = foldl' insert []
  where
    insert found g
      | any (same g) found || any (same g) seen = found
      | otherwise = g : found

-- The map stores transitive reachability without reflexive pairs. Adding
-- u → v connects every predecessor of u to every successor of v.
maximalPathRelations :: Graph s l -> [(Int, Int)] -> [[(Int, Int)]]
maximalPathRelations (Graph ns ins outs bs) forbidden =
  [ relation
  | sound initial
  , (relation, reach) <- search [] initial candidates
  , all (\edge -> edge `elem` relation || isNothing (addPath reach edge)) candidates
  ]
  where
    edges = wireEdges bs
    initial = IM.fromDistinctAscList [(i, IS.delete i (reachableNodes edges i)) | i <- [0 .. length ns - 1]]
    candidates = [edge | o <- outs, i <- ins, let edge = (o, i), isJust (addPath initial edge)]
    sound reach = all (\(o, i) -> IS.notMember i (reach IM.! o)) forbidden
    addPath reach (u, v)
      | u == v || IS.member u (reach IM.! v) = Nothing
      | otherwise = updated <$ guard (sound updated)
      where
        targets = IS.insert v (reach IM.! v)
        updated = IM.mapWithKey (\i row -> if i == u || IS.member u row then IS.union row targets else row) reach
    search relation reach remaining =
      let viable = filter (isJust . addPath reach) remaining
      in case foldM addPath reach viable of
           Just complete -> [(relation ++ viable, complete)]
           Nothing -> case viable of
             [] -> []
             edge : rest ->
               [result | extended <- maybeToList (addPath reach edge), result <- search (edge : relation) extended rest]
                 ++ search relation reach rest

-- Fan-out and fan-in boxes give one private wire to each selected relation
-- edge. Unique marker labels pin their attachments during isomorphism checks.
pathExtension :: Graph s l -> [(Int, Int)] -> Graph s (Either Int l)
pathExtension (Graph ns ins outs bs) relation =
  Graph
    sorts'
    (filter (`IM.notMember` toward) ins)
    (filter (`IM.notMember` from) outs)
    (map (\b -> b{label = Right (label b)}) bs ++ fanOut ++ fanIn)
  where
    numbered = zip [length ns ..] relation
    sorts' = ns ++ [ns !! o | (_, (o, _)) <- numbered]
    from = IM.fromListWith (++) [(o, [n]) | (n, (o, _)) <- numbered]
    toward = IM.fromListWith (++) [(i, [n]) | (n, (_, i)) <- numbered]
    fanOut = [Box (Left o) [o] wires | (o, wires) <- IM.toList from]
    fanIn = [Box (Left i) wires [i] | (i, wires) <- IM.toList toward]

-- | Normalise a monogamous acyclic string diagram using one convex match at
-- a time. Each successful step counts as one rewrite and one batch. Use
-- 'Proarrow.Tools.HypergraphRewrite.unlimitedRewrites' when the rules are known to terminate, and
-- 'checkPathContexts' to check whether different rewrite choices rejoin.
normaliseConvex
  :: forall {s} l as bs
   . (Eq l, DecidableIso s)
  => RewriteLimits
  -> ConvexRules s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> Either String (NormalisationResult (Wires as ~> (Wires bs :: OPENHG s l)))
normaliseConvex limits rules host
  | validDiagram (graph host) = Right (normaliseBy limits (take 1 . convexMatches rules) host)
  | otherwise = Left "normaliseConvex: the host must be a monogamous acyclic diagram"
