module Props.HypergraphRewrite.Completion (test) where

import Control.Monad (forM_)
import Data.List (sort)
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.OpenHypergraph (W1, W2)
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
    , testProperty "hypergraph completion removes redundant rules and simplifies right sides" checkHypergraphInterreduction
    ]

type Diagram l as bs = (HG.Wires as :: HG.OPENHG () l) ~> HG.Wires bs

type Wire l = HG.Wires @() @l W1

wire :: Wire l ~> Wire l
wire = id

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
