-- | A fragment of the special commutative Frobenius presentation, interpreted
-- as finite-set cospans with one apex point per generator.
module Examples.KnuthBendix.Frobenius (test) where

import Control.Monad (forM_, join)
import Data.Kind (Type)
import Data.List (sort)
import Data.Set qualified as Set
import Data.Void (Void)
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.OpenHypergraph (W1, W2)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Monoidal (MonoidalProfunctor ((**)), SymMonoidal (swap))
import Proarrow.Core (Promonad (id, (.)), obj, type (~>))
import Proarrow.Monoid qualified as Mon
import Proarrow.Testing (check, expect)
import Proarrow.Tools.HypergraphRewrite ((==>))
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion

data Generator l = Multiply | Unit | Comultiply | Counit | Label l
  deriving (Eq)

type Graph :: Type -> [()] -> [()] -> Type
type Graph l as bs = (HG.Wires as :: HG.OPENHG () l) ~> HG.Wires bs

type Diagram :: Type -> [()] -> [()] -> Type
type Diagram l as bs = Graph (Generator l) as bs

multiply :: Diagram l W2 W1
multiply = HG.box Multiply

unit :: Diagram l '[] W1
unit = HG.box Unit

comultiply :: Diagram l W1 W2
comultiply = HG.box Comultiply

counit :: Diagram l W1 '[]
counit = HG.box Counit

wire :: Graph l W1 W1
wire = obj

mergeSplit :: Diagram l W2 W2
mergeSplit = comultiply . multiply

splitMerge :: Diagram l W1 W1
splitMerge = multiply . comultiply

frobeniusRight :: Diagram l W2 W2
frobeniusRight = (multiply ** wire) . (wire ** comultiply)

frobeniusRules :: Either String [R.Rule () (Generator Void)]
frobeniusRules =
  sequence
    [ mergeSplit ==> frobeniusRight
    , mergeSplit ==> (wire ** multiply) . (comultiply ** wire)
    , splitMerge ==> wire
    ]

type Point :: forall l. HG.OPENHG () l
type Point @l = HG.Wires @() @l W1

-- An open hypergraph with Void labels is a finite-set cospan. The canonical
-- operations on a one-point object identify the ports of each Frobenius box.
absorbFrobenius :: forall l as bs. Diagram l as bs -> Either String (Graph l as bs)
absorbFrobenius = HG.substitute interpret
  where
    interpret Multiply = HG.SomeHypergraph (Mon.mappend @(Point @l))
    interpret Unit = HG.SomeHypergraph (Mon.mempty @(Point @l))
    interpret Comultiply = HG.SomeHypergraph (Mon.comult @(Point @l))
    interpret Counit = HG.SomeHypergraph (Mon.counit @(Point @l))
    interpret (Label label) = HG.SomeHypergraph (HG.box @l @W1 @W1 label)

checkCospans :: String -> Diagram Void as bs -> Diagram Void as bs -> Property ()
checkCospans label lhs rhs = do
  left <- either testFailed pure (absorbFrobenius lhs)
  right <- either testFailed pure (absorbFrobenius rhs)
  check label (HG.isomorphic left right)

compareReducts :: (a :: HG.OPENHG () (Generator l)) ~> b -> a ~> b -> Ordering
compareReducts l r = compare (measure l) (measure r)
  where
    measure g =
      let (_, _, _, boxes) = HG.hypergraphParts g
          mergeSplits = length [() | HG.Box Multiply _ [v] <- boxes, HG.Box Comultiply [w] _ <- boxes, v == w]
      in (mergeSplits, length boxes)

checkSpecialCompletion :: Property ()
checkSpecialCompletion = do
  let withUnit = multiply . (wire ** unit)
  rightUnit <- either testFailed pure (withUnit ==> wire)
  expanded <- either testFailed pure (splitMerge . withUnit ==> wire)
  result <- either testFailed pure (Completion.completeConvex 1 8 compareReducts [rightUnit, expanded])
  case result of
    Completion.ConvexComplete final compiled -> do
      expect "the unit rule and learned special rule remain" 2 (length final)
      normal <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled splitMerge)
      expect "the special rule contracts split-then-merge in one step" 1 (R.normalisationRewrites normal)
      check "split-then-merge reduces to a wire" (HG.isomorphic wire (R.normalisedGraph normal))
      checkCospans "the learned contraction preserves its cospan" splitMerge (R.normalisedGraph normal)
    _ -> testFailed "expected completion to recover the special rule"

data Toggle = Toggle
  deriving (Eq)

checkLabelledRewrite :: Property ()
checkLabelledRewrite = do
  let labelled = HG.box @(Generator Toggle) @W1 @W1 (Label Toggle)
      toggle = HG.box @Toggle @W1 @W1 Toggle
      inputs = (labelled . splitMerge . labelled) ** labelled
      lhs = mergeSplit . inputs
      rhs = frobeniusRight . inputs
  syntaxRule <- either testFailed pure (labelled . labelled ==> wire)
  check "the explicit split and merge separate the two toggles" (null (R.rewrites syntaxRule lhs))
  check "the two drawings differ before absorbing Frobenius wiring" (not (HG.isomorphic lhs rhs))
  left <- either testFailed pure (absorbFrobenius lhs)
  right <- either testFailed pure (absorbFrobenius rhs)
  check "the two drawings give the same labelled cospan" (HG.isomorphic left right)
  cancel <- either testFailed pure (toggle . toggle ==> wire)
  compiled <- either testFailed pure (R.compileRules [((), cancel)])
  expected <- either testFailed pure (absorbFrobenius (mergeSplit . (wire ** labelled)))
  forM_ [left, right] \graph -> do
    let result = R.normalise R.unlimitedRewrites compiled graph
    expect "one pair of toggles cancels" 1 (R.normalisationRewrites result)
    check "the other toggle and its wiring remain" (HG.isomorphic expected (R.normalisedGraph result))

type Predicate = Set.Set Char

-- A predicate consumes a wire. Multiple predicates can test the same wire
-- because the Frobenius copy is already part of the cospan wiring.
checksAtJunction :: [Predicate] -> Graph Predicate W1 '[]
checksAtJunction [] = Mon.counit @(Point @Predicate)
checksAtJunction (p : ps) =
  (HG.box @Predicate @W1 @'[] p ** checksAtJunction ps) . Mon.comult @(Point @Predicate)

fuseChecks :: (Predicate, Predicate) -> Either String (R.Rule () Predicate)
fuseChecks (p, q) = checksAtJunction [p, q] ==> checksAtJunction [p <> q]

checkJunctionOverlap :: Property ()
checkJunctionOverlap = do
  let a = Set.singleton 'a'
      b = Set.singleton 'b'
      c = Set.singleton 'c'
  rules <- either testFailed pure (traverse fuseChecks [(a, b), (b, c), (a <> b, c), (a, b <> c)])
  let named = zip [0 :: Int ..] rules
  compiled <- either testFailed pure (R.compileReducingRules named)
  peaks <- either testFailed pure (Completion.hypergraphOverlaps (take 2 named))
  let mixed = [peak | peak@(Completion.CriticalOverlap first second _ _ _) <- peaks, first /= second]
  case mixed of
    [Completion.CriticalOverlap 0 1 fork left right] -> do
      let (nodes, ins, outs, boxes) = HG.hypergraphParts fork
      expect
        "one shared junction with three tests"
        (1, [0], [], [a, b, c])
        (length nodes, ins, outs, sort (map HG.label boxes))
      check "the two single-step reducts differ" (not (HG.isomorphic left right))
      expect "the two matches compete for one occurrence of b" 1 (fst (R.rewriteBatchCompiled compiled fork))
      forM_ [left, right] \branch -> do
        let normal = R.normalise R.unlimitedRewrites compiled branch
            (_, _, _, result) = HG.hypergraphParts (R.normalisedGraph normal)
        expect "one more fusion joins the overlap" 1 (R.normalisationRewrites normal)
        expect "all three tests fuse into one" [HG.Box (a <> b <> c) [0] []] result
    _ -> testFailed "expected one overlap sharing the test for b"
  let (count, separate) = R.rewriteBatchCompiled compiled (checksAtJunction [a, b, b, c])
  expect "distinct occurrences of b allow both fusions" 2 count
  check "both fusions preserve the shared junction" (HG.isomorphic (checksAtJunction [a <> b, b <> c]) separate)

checkIsolatedNodeOverlap :: Property ()
checkIsolatedNodeOverlap = do
  let discard = Mon.counit @(Point @Predicate)
      closed = discard . Mon.mempty @(Point @Predicate)
      empty = id :: Graph Predicate '[] '[]
  erase <- either testFailed pure (closed ==> empty)
  attach <- either testFailed pure (discard ==> checksAtJunction [Set.singleton 'a'])
  peaks <- either testFailed pure (Completion.hypergraphOverlaps [(False, erase), (True, attach)])
  case peaks of
    [Completion.CriticalOverlap False True host left right] -> do
      let (hostNodes, ins, outs, hostBoxes) = HG.hypergraphParts host
          (leftNodes, _, _, _) = HG.hypergraphParts left
          (_, _, _, rightBoxes) = HG.hypergraphParts right
      expect "the deletable node is internal and isolated" (1, [], [], 0) (length hostNodes, ins, outs, length hostBoxes)
      expect "one step erases the node" 0 (length leftNodes)
      expect "the other step attaches a box to the node" 1 (length rightBoxes)
    _ -> testFailed "expected an overlap on the isolated node"

checkJunctionCompletion :: Property ()
checkJunctionCompletion = do
  let a = Set.singleton 'a'
      b = Set.singleton 'b'
      c = Set.singleton 'c'
      measure g =
        let (_, _, _, boxes) = HG.hypergraphParts g
        in (length boxes, length (filter ((== a <> b) . HG.label) boxes))
      comparePredicates l r = compare (measure l) (measure r)
  seeds <- either testFailed pure (traverse fuseChecks [(a, b), (b, c)])
  pending <- either testFailed pure (Completion.completeHypergraph 0 8 comparePredicates seeds)
  () <- case pending of
    Completion.HypergraphIncomplete _ (Completion.HypergraphRuleLimit (Completion.CriticalOverlap 0 1 _ _ _)) -> pure ()
    _ -> testFailed "expected the overlap on b before learning a rule"
  completed <- either testFailed pure (Completion.completeHypergraph 1 8 comparePredicates seeds)
  case completed of
    Completion.HypergraphComplete final compiled -> do
      expect "the completed presentation adds one rule" 3 (length final)
      let from = checksAtJunction [a <> b, c]
          to = checksAtJunction [a, b <> c]
      case R.rewritesCompiled compiled from of
        [(2, reduct)] -> check "the learned rule joins the two fusions" (HG.isomorphic to reduct)
        _ -> testFailed "expected the learned rule on the first reduct"
      let normal = R.normalise (R.RewriteLimits (Just 8) Nothing) compiled (checksAtJunction [a, b, c])
      expect "the three predicates reach normal form" R.NormalForm (R.normalisationStatus normal)
      check "the overlap normalises to the preferred fusion" (HG.isomorphic to (R.normalisedGraph normal))
    _ -> testFailed "expected the junction presentation to complete with one learned rule"

checkIdentifiedJunctions :: Property ()
checkIdentifiedJunctions = do
  let a = Set.singleton 'a'
      b = Set.singleton 'b'
      c = Set.singleton 'c'
      at p = checksAtJunction [p]
      discard = Mon.counit @(Point @Predicate)
      fuse (p, q) = at p ** at q ==> at (p <> q) ** discard
      separated = at a ** at b ** at c
      swapWires = swap @_ @(Point @Predicate) @(Point @Predicate)
      identify = (wire ** swapWires) . (Mon.comult @(Point @Predicate) ** wire)
      identified = separated . identify
  rules <- either testFailed pure (traverse fuse [(a, b), (c, b), (a <> b, c), (a, b <> c)])
  let named = zip [0 :: Int ..] rules
  compiled <- either testFailed pure (R.compileReducingRules named)
  expect "both matches survive the Frobenius identification" [0, 1] (map fst (R.rewritesCompiled compiled identified))
  peaks <- either testFailed pure (Completion.hypergraphOverlaps (take 2 named))
  let normal :: Graph Predicate as bs -> R.NormalisationResult (Graph Predicate as bs)
      normal = R.normalise R.unlimitedRewrites compiled
      joined =
        [ ( length nodes
          , R.normalisationRewrites l
          , R.normalisationRewrites r
          , HG.isomorphic (R.normalisedGraph l) (R.normalisedGraph r)
          )
        | Completion.CriticalOverlap 0 1 host left right <- peaks
        , let (nodes, _, _, _) = HG.hypergraphParts host
              l = normal left
              r = normal right
        ]
  expect
    "the identified branches are irreducible and the separate branches join"
    [(2, 0, 0, False), (3, 1, 1, True)]
    (sort joined)

checkMergingRuleOverlap :: Property ()
checkMergingRuleOverlap = do
  let discard = Mon.counit @(Point @Predicate)
      merge = discard . Mon.mappend @(Point @Predicate)
      marker label = HG.box @Predicate @W2 @'[] (Set.singleton label)
      copy = Mon.comult @(Point @Predicate)
      swapWires = swap @_ @(Point @Predicate) @(Point @Predicate)
      host = (marker 'a' ** marker 'b') . (wire ** swapWires ** wire) . (copy ** copy)
  identify <- either testFailed pure (marker 'a' ==> merge)
  erase <- either testFailed pure (marker 'b' ==> discard ** discard)
  let rules = [(False, identify), (True, erase)]
  compiled <- either testFailed pure (R.compileReducingRules rules)
  case R.rewritesCompiled compiled host of
    [(False, merged), (True, erased)] -> do
      expect "merging disables the match for b" [] (map fst (R.rewritesCompiled compiled merged))
      case R.rewritesCompiled compiled erased of
        [(False, result)] -> check "erasing first still allows the merge" (HG.isomorphic merge result)
        _ -> testFailed "expected a merge after erasing b"
    _ -> testFailed "expected two matches on disjoint boxes"
  let (count, batched) = R.rewriteBatchCompiled compiled host
  expect "the simultaneous batch applies both matches" 2 count
  check "the batch agrees with erasing before merging" (HG.isomorphic merge batched)
  peaks <- either testFailed pure (Completion.hypergraphOverlaps rules)
  let mixed = [peak | peak@(Completion.CriticalOverlap False True _ _ _) <- peaks]
  expect "both ways of sharing the two junctions give an overlap" 2 (length mixed)
  forM_ mixed \(Completion.CriticalOverlap _ _ source merged erased) -> do
    let (nodes, ins, outs, boxes) = HG.hypergraphParts source
    expect "two junctions and two boxes" (2, [0, 1], [], 2) (length nodes, ins, outs, length boxes)
    expect "the merged branch is stuck" [] (map fst (R.rewritesCompiled compiled merged))
    expect "the erased branch can merge" [False] (map fst (R.rewritesCompiled compiled erased))
  before <- either testFailed pure (Completion.checkHypergraphConfluence Nothing rules)
  case before of
    Completion.HypergraphNotLocallyConfluent (Completion.CriticalOverlap False True _ _ _) -> pure ()
    _ -> testFailed "expected the merge and erase rules to be locally nonconfluent"
  let boxCount g = let (_, _, _, boxes) = HG.hypergraphParts g in length boxes
  completion <-
    either testFailed pure (Completion.completeHypergraph 1 8 (\l r -> compare (boxCount l) (boxCount r)) [identify, erase])
  case completion of
    Completion.HypergraphIncomplete _ (Completion.HypergraphUnorientable reason _) ->
      testFailed ("could not complete the merged boundary: " ++ reason)
    Completion.HypergraphComplete final@[_, _, repair] completed -> do
      check "the learned rule requires b's ports to share a junction" (null (R.rewrites repair host))
      forM_ mixed \(Completion.CriticalOverlap _ _ _ merged erased) ->
        case (R.rewrites repair merged, R.rewrites identify erased) of
          ([repaired], [joined]) -> do
            let (points, inputs, outputs, boxes) = HG.hypergraphParts repaired
            expect "both ports still attach to the shared junction" (1, [0, 0], [], []) (length points, inputs, outputs, boxes)
            check "the learned rule joins the overlap" (HG.isomorphic joined repaired)
          _ -> testFailed "expected one step from each branch to the joined graph"
      let finalRules = zip [0 :: Int ..] final
      shallow <- either testFailed pure (Completion.checkHypergraphConfluence (Just 0) finalRules)
      case shallow of
        Completion.HypergraphConfluenceLimit _ -> pure ()
        _ -> testFailed "expected the completed system to need a joining step"
      checked <- either testFailed pure (Completion.checkHypergraphConfluence Nothing finalRules)
      case checked of
        Completion.HypergraphLocallyConfluent overlapCount -> check "overlaps checked" (overlapCount >= length mixed)
        _ -> testFailed "expected the completed system to be locally confluent"
      -- The context box shares both junctions. Merging them must also merge
      -- its two attachments, while leaving the box outside the rewrite.
      let inContext g = (g ** marker 'c') . (wire ** swapWires ** wire) . (copy ** copy)
          expected = inContext merge
      case R.rewritesCompiled completed (inContext host) of
        [(0, merged), (1, erased)] ->
          forM_ [merged, erased] \branch -> case R.rewritesCompiled completed branch of
            [(_, joined)] ->
              check "the join lifts through a box attached to both junctions" (HG.isomorphic expected joined)
            _ -> testFailed "expected one joining step in the context"
        _ -> testFailed "expected both initial steps to lift into the context"
    _ -> testFailed "expected completion to learn one single-junction rule"

checkDifferentBoundaries :: Property ()
checkDifferentBoundaries = do
  let marker = HG.box @Predicate @W2 @'[] (Set.singleton 'a')
      discard = Mon.counit @(Point @Predicate)
      measure g = let (nodes, _, _, boxes) = HG.hypergraphParts g in (length boxes, negate (length nodes))
  identify <- either testFailed pure (marker ==> discard . Mon.mappend @(Point @Predicate))
  erase <- either testFailed pure (marker ==> discard ** discard)
  -- Resolve the overlap on parallel markers so the remaining fork compares
  -- the two replacements of a single marker.
  eraseLoop <- either testFailed pure (marker . Mon.comult @(Point @Predicate) ==> discard)
  result <-
    either
      testFailed
      pure
      (Completion.completeHypergraph 1 8 (\l r -> compare (measure l) (measure r)) [identify, erase, eraseLoop])
  case result of
    Completion.HypergraphIncomplete
      retained
      (Completion.HypergraphUnorientable reason (Completion.CriticalOverlap 0 1 _ _ _)) -> do
        expect "no rule was learned" 3 (length retained)
        expect
          "the two reducts disagree on boundary equality"
          "completion: the reducts identify different boundary ports"
          reason
    _ -> testFailed "expected completion to report incompatible boundary identifications"

test :: TestTree
test =
  testGroup
    "Special commutative Frobenius diagrams"
    [ testProperty "Frobenius and special equations preserve finite-set cospans" $ do
        rules <- either testFailed pure frobeniusRules
        forM_ rules \rule ->
          join (either testFailed pure (Completion.withFixedRule rule (checkCospans "the cospans agree")))
        -- A connected closed component has one apex point and no boundary.
        closed <- either testFailed pure (absorbFrobenius @Void (counit . unit))
        let (points, ins, outs, boxes) = HG.hypergraphParts closed
        expect "closed component" (1, [], [], 0) (length points, ins, outs, length boxes)
    , testProperty "completion learns the special rule from the right-unit overlap" checkSpecialCompletion
    , testProperty "the Frobenius overlap ties on the reduction measure but agrees as a cospan" $ do
        rules <- either testFailed pure frobeniusRules
        result <- either testFailed pure (Completion.completeConvex 1 8 compareReducts rules)
        case result of
          Completion.ConvexIncomplete _ (Completion.ConvexUnorientable _ (Completion.CriticalOverlap 0 1 _ left right)) -> do
            expect "both Frobenius branches have the same measure" EQ (compareReducts left right)
            check "the two Frobenius branches differ as graphs" (not (HG.isomorphic left right))
            checkCospans "the two Frobenius branches agree as cospans" left right
          _ -> testFailed "expected the two Frobenius rules to tie on the reduction measure"
    , testProperty "labelled rewriting is independent of the Frobenius drawing" checkLabelledRewrite
    , testProperty "fusions at a shared junction conflict only when they share a box" checkJunctionOverlap
    , testProperty "an overlap can share a node without sharing a box" checkIsolatedNodeOverlap
    , testProperty "bounded completion joins the predicate fusions with one learned rule" checkJunctionCompletion
    , testProperty "overlap enumeration finds a fork made unjoinable by Frobenius wiring" checkIdentifiedJunctions
    , testProperty "a rule can disable a disjoint match by merging its junctions" checkMergingRuleOverlap
    , testProperty "completion reports incompatible boundary identifications" checkDifferentBoundaries
    ]
