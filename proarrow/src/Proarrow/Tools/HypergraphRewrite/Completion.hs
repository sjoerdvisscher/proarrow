-- | Critical overlaps and bounded Knuth–Bendix-style completion for fixed
-- rules. Convex rewriting works with monogamous acyclic string diagrams and
-- checks all maximal path contexts. Hypergraph completion uses the ordinary
-- matcher with shared Frobenius wiring.
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

import Control.Monad (foldM, guard, unless)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Type)
import Data.List (tails)
import Data.List qualified as List
import Data.Maybe (fromMaybe, isJust, isNothing, maybeToList)
import Numeric.Natural (Natural)
import Prelude

import Proarrow.Category.Instance.OpenHypergraph (Box (..), OPENHG, Wires, reifySorts, sameSort, unsafeOpenHypergraph)
import Proarrow.Core (CategoryOf (..), Kind)
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Tools.HypergraphRewrite
  ( CompiledRules
  , NormalisationResult (..)
  , NormalisationStatus (NormalForm)
  , RewriteLimits (..)
  , compileRules
  )
import Proarrow.Tools.HypergraphRewrite.Internal
  ( Graph (..)
  , LabelTest (..)
  , Match
  , Prepared
  , Rule (..)
  , deletedImages
  , graph
  , mapLabels
  , matches
  , nonConflictingBy
  , normaliseBy
  , normaliseGraphBy
  , replaceMany
  , rule
  , sameGraph
  , traverseLabels
  )
import Proarrow.Tools.HypergraphRewrite.Internal.Matcher (compiledMatches)

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
    HypergraphOverlaps -> pure ()
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

-- A replacement can identify nodes that another match needs to keep distinct.
identifiesMatchNodes :: Graph s l -> Graph s l -> Match -> Match -> Bool
identifiesMatchNodes (Graph _ li lo _) (Graph _ ri ro _) (mapping, _) (other, _) =
  length targets /= IS.size (IS.fromList targets)
  where
    readNodes = IS.fromList (IM.elems other)
    targets = [r | (l, r) <- zip (li ++ lo) (ri ++ ro), IS.member (mapping IM.! l) readNodes]

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

type PairCheck :: Type -> Kind -> Type -> Type
data PairCheck key s l
  = AllJoinable Int
  | Unjoinable (PreCriticalPair key s l)
  | JoinLimit (PreCriticalPair key s l)

checkPairs
  :: (Eq l, DecidableIso s)
  => Maybe Natural -> (Graph s l -> [Graph s l]) -> [PreCriticalPair key s l] -> PairCheck key s l
checkPairs maxDepth reducts = checkAll 0 Nothing
  where
    checkAll count pending [] = maybe (AllJoinable count) JoinLimit pending
    checkAll count pending (pair@(host, left, right) : more) =
      case joinGraphs maxDepth reducts (applyStep host left) (applyStep host right) of
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
joinGraphs maxDepth next left right = search maxDepth [] [left] [] [right]
  where
    search depth seenL frontL seenR frontR
      | any (\g -> any (sameGraph g) (frontR ++ seenR)) frontL
          || any (\g -> any (sameGraph g) seenL) frontR =
          Just True
      | null frontL && null frontR = Just False
      | otherwise =
          let (seenL', frontL') = advance seenL frontL
              (seenR', frontR') = advance seenR frontR
          in case depth of
               Just 0 -> if null frontL' && null frontR' then Just False else Nothing
               _ -> search (subtract 1 <$> depth) seenL' frontL' seenR' frontR'
    advance seen front = (seen', fresh)
      where
        seen' = front ++ seen
        fresh = foldl' insert [] (concatMap next front)
        insert found g
          | any (sameGraph g) found || any (sameGraph g) seen' = found
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
