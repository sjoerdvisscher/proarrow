{-# LANGUAGE AllowAmbiguousTypes #-}

module Props.HypergraphRewrite (test) where

import Control.Monad (replicateM)
import Data.Either (isLeft)
import Data.List (permutations, sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as M
import Data.Type.Nat (Nat2, Nat3)
import Test.Falsify (Property, testFailed)
import Test.Falsify qualified as Falsify
import Test.Falsify.Generator qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Instance.Mat (MatK (..))
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , OPENHG
  , SortList
  , W1
  , W2
  , W3
  , Wires
  , isomorphic
  , sortList
  , unsafeOpenHypergraph
  )
import Proarrow.Core (CategoryOf (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.HypergraphRewrite
  ( NormalisationResult (..)
  , NormalisationStatus (..)
  , Parameter (..)
  , RewriteLimits (..)
  , Rule
  , compileReducingRules
  , compileRules
  , mapParameter
  , normalise
  , parameterRule
  , rewriteBatch
  , rewriteBatchCompiled
  , rewrites
  , rewritesCompiled
  , rule
  , unlimitedRewrites
  )
import Proarrow.Tools.HypergraphRewrite qualified as R

type OH = OPENHG (MatK Int) String
type Closed = Wires '[] :: OH
type Open = Wires '[M Nat2] :: OH

diagram
  :: (SortList as, SortList bs)
  => Int -> [Int] -> [Int] -> [Box String Int] -> (Wires as :: OH) ~> Wires bs
diagram n = unsafeOpenHypergraph (concat (replicate n (sortList @_ @'[M Nat2])))

chain :: Open ~> Open
chain = diagram 3 [0] [2] [Box "not" [0] [1], Box "not" [1] [2]]

wire :: Open ~> Open
wire = diagram 1 [0] [0] []

withCancellation :: (Rule (MatK Int) String -> Property ()) -> Property ()
withCancellation k = case rule chain wire of
  Left err -> testFailed err
  Right r -> k r

expectOnly :: Closed ~> Closed -> [Closed ~> Closed] -> Property ()
expectOnly expected actual = do
  expect "one rewrite" 1 (length actual)
  check "unexpected result" (all (isomorphic expected) actual)

-- Exhaustive two-edge path elimination on four nodes. This small oracle uses
-- ordered edge pairs and direct node substitution, without matcher indices.
referenceCancellation :: [Box String Int] -> [Closed ~> Closed]
referenceCancellation bs =
  [ diagram 2 [] [] (map (fmap rename) remaining)
  | (i, Box "not" [x] [y]) <- numbered
  , (j, Box "not" [y'] [z]) <- numbered
  , i /= j
  , y == y'
  , x /= y
  , y /= z
  , x /= z
  , let remaining = [b | (k, b) <- numbered, k /= i, k /= j]
  , all (\b -> y `notElem` (inputs b ++ outputs b)) remaining
  , let indices = M.fromList (zip [n | n <- [0 .. 3], n /= y, n /= z] [0 ..])
        rename n = indices M.! (if n == z then x else n)
  ]
  where
    numbered = zip [0 :: Int ..] bs

test :: TestTree
test =
  testGroup
    "HypergraphRewrite"
    [ portTests
    , parameterTests
    , reducingTests
    , subgraphTests
    , testProperty "closed cancellation joins interface nodes and retains isolated nodes" $
        withCancellation $ \r ->
          expectOnly
            (diagram 2 [] [] [Box "source" [] [0], Box "sink" [0] []])
            ( rewrites
                r
                (diagram 4 [] [] [Box "source" [] [0], Box "not" [0] [1], Box "not" [1] [2], Box "sink" [2] []] :: Closed ~> Closed)
            )
    , testProperty "indexed cancellation agrees with exhaustive edge pairs" $
        withCancellation $ \r -> do
          size <- Falsify.gen (Gen.elem (0 :| [1 .. 6]))
          boxes <- replicateM size $ do
            label <- Falsify.gen (Gen.elem ("not" :| ["other"]))
            a <- Falsify.gen (Gen.elem (0 :| [1 .. 3]))
            b <- Falsify.gen (Gen.elem (0 :| [1 .. 3]))
            pure (Box label [a] [b])
          let expected = referenceCancellation boxes
              actual = rewrites r (diagram 4 [] [] boxes :: Closed ~> Closed)
          expect "match multiplicity" (length expected) (length actual)
          check "match results or order changed" (and (zipWith isomorphic expected actual))
    , testProperty "matches retain host box order rather than node order" $ do
        let gate = diagram 2 [0] [1] [Box "not" [0] [1]] :: Open ~> Open
            done = diagram 2 [0] [1] [Box "done" [0] [1]] :: Open ~> Open
            tagged right left =
              diagram
                4
                []
                []
                [ Box "left source" [] [0]
                , Box "right source" [] [2]
                , Box right [2] [3]
                , Box left [0] [1]
                , Box "left sink" [1] []
                , Box "right sink" [3] []
                ]
                :: Closed ~> Closed
        case rule gate done of
          Left err -> testFailed err
          Right r -> case rewrites r (tagged "not" "not") of
            [first, second] -> do
              check "right occurrence must come first" (isomorphic (tagged "done" "not") first)
              check "left occurrence must come second" (isomorphic (tagged "not" "done") second)
            xs -> testFailed ("expected two matches, got " ++ show (length xs))
    , testProperty "repeated ports must still map to one node" $ do
        let lhs = diagram 2 [0] [1] [Box "repeat" [0] [1, 1]] :: Open ~> Open
            host = diagram 4 [] [] [Box "repeat" [0] [1, 2], Box "repeat" [0] [3, 3]] :: Closed ~> Closed
        case rule lhs wire of
          Left err -> testFailed err
          Right r -> expectOnly (diagram 3 [] [] [Box "repeat" [0] [1, 2]]) (rewrites r host)
    , testProperty "disconnected pattern boxes use independent candidates" $ do
        let lhs = diagram 4 [] [] [Box "a" [0] [1], Box "b" [2] [3]] :: Closed ~> Closed
            rhs = diagram 0 [] [] [] :: Closed ~> Closed
            host = diagram 5 [] [] [Box "b" [3] [4], Box "a" [1] [2]] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> expectOnly (diagram 1 [] [] []) (rewrites r host)
    , testProperty "all known input and output ports constrain candidates" $ do
        let lhs = diagram 3 [0, 1] [2] [Box "fork" [0] [1, 2], Box "join" [1, 2] [0]] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open
            rhs = diagram 3 [0, 1] [2] [Box "done" [0, 1] [2]] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open
            host = diagram 3 [] [] [Box "fork" [0] [1, 2], Box "join" [2, 1] [0], Box "join" [1, 2] [0]] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> expectOnly (diagram 3 [] [] [Box "join" [2, 1] [0], Box "done" [0, 1] [2]]) (rewrites r host)
    , testProperty "an unmatched attachment prevents deletion of an internal node" $
        withCancellation $ \r ->
          expect
            "no rewrite"
            0
            (length (rewrites r (diagram 3 [] [] [Box "not" [0] [1], Box "not" [1] [2], Box "tap" [1] []] :: Closed ~> Closed)))
    , testProperty "the host boundary prevents deletion of an internal node" $
        withCancellation $ \r ->
          expect "no rewrite" 0 (length (rewrites r (diagram 3 [1] [2] [Box "not" [0] [1], Box "not" [1] [2]] :: Open ~> Open)))
    , testProperty "open cancellation preserves repeated host boundary attachments" $
        withCancellation $ \r -> do
          let host = diagram 3 [0, 0] [2] [Box "not" [0] [1], Box "not" [1] [2]] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open
              expected = diagram 1 [0, 0] [0] [] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open
              results = rewrites r host
          expect "one rewrite" 1 (length results)
          check "boundary attachments changed" (all (isomorphic expected) results)
    , testProperty "sort parameters instantiate replacements from the matched host" $
        withCancellation \r -> do
          let host =
                unsafeOpenHypergraph
                  (sortList @_ @'[M Nat3, M Nat3, M Nat3])
                  []
                  []
                  [Box "not" [0] [1], Box "not" [1] [2]]
                  :: Closed ~> Closed
              expected = unsafeOpenHypergraph (sortList @_ @'[M Nat3]) [] [] [] :: Closed ~> Closed
              adapt _ actual rhs = case actual of
                first : _ -> Just (replicate (length rhs) first)
                [] -> Nothing
              generic = R.withSortParameters adapt r
          expectOnly expected (rewrites generic host)
    , testProperty "sort instantiation cannot change interface types or node counts" $
        withCancellation \r -> do
          let host =
                unsafeOpenHypergraph
                  (sortList @_ @'[M Nat3, M Nat3, M Nat3])
                  []
                  []
                  [Box "not" [0] [1], Box "not" [1] [2]]
                  :: Closed ~> Closed
              wrongType = R.withSortParameters (\_ _ rhs -> Just rhs) r
              wrongCount = R.withSortParameters (\_ _ _ -> Just []) r
          expect "interface sort change rejected" 0 (length (rewrites wrongType host))
          expect "missing replacement sort rejected" 0 (length (rewrites wrongCount host))
    , testProperty "sort parameters also instantiate port-rule replacements" $ do
        let lhs =
              R.PortGraph
                (sortList @_ @'[M Nat2, M Nat2, M Nat2])
                [0, 2]
                [Box "not" [R.Node 0] [R.Node 1], Box "not" [R.Node 1] [R.Node 2]]
            rhs = R.PortGraph (sortList @_ @'[M Nat2]) [0, 0] []
            host =
              unsafeOpenHypergraph
                (sortList @_ @'[M Nat3, M Nat3, M Nat3])
                []
                []
                [Box "not" [0] [1], Box "not" [1] [2]]
                :: Closed ~> Closed
            expected = unsafeOpenHypergraph (sortList @_ @'[M Nat3]) [] [] [] :: Closed ~> Closed
        r <- either testFailed pure (R.portRule lhs rhs)
        let generic = R.withSortParameters (\_ actual _ -> Just (take 1 actual)) r
        expectOnly expected (rewrites generic host)
    , testProperty "matching respects sorts" $
        withCancellation $ \r -> do
          let host =
                unsafeOpenHypergraph (sortList @_ @'[M Nat3, M Nat3, M Nat3]) [] [] [Box "not" [0] [1], Box "not" [1] [2]]
                  :: Closed ~> Closed
          expect "no rewrite" 0 (length (rewrites r host))
    , testProperty "a loop cannot identify distinct pattern nodes" $
        withCancellation $ \r ->
          expect "no rewrite" 0 (length (rewrites r (diagram 2 [] [] [Box "not" [0] [1], Box "not" [1] [0]] :: Closed ~> Closed)))
    , testProperty "noninjective left interfaces are rejected" $
        check "accepted a noninjective left interface" (isLeft (rule wire chain))
    , testProperty "isolated pattern nodes match only deletable host nodes" $ do
        let lhs = diagram 1 [] [] [] :: Closed ~> Closed
            rhs = diagram 0 [] [] [] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r ->
            expectOnly
              (diagram 1 [] [] [Box "loop" [0] [0]])
              (rewrites r (diagram 2 [] [] [Box "loop" [0] [0]] :: Closed ~> Closed))
    , testProperty "nullary boxes can be removed without removing nodes" $ do
        let lhs = diagram 0 [] [] [Box "scalar" [] []] :: Closed ~> Closed
            rhs = diagram 0 [] [] [] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r ->
            expectOnly
              (diagram 1 [] [] [])
              (rewrites r (diagram 1 [] [] [Box "scalar" [] []] :: Closed ~> Closed))
    , testProperty "matching preserves port order" $ do
        let lhs = diagram 3 [0, 1] [2] [Box "pair" [0, 1] [2], Box "anchor" [] [0]] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open
            rhs = diagram 3 [0, 1] [2] [] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open
            host = diagram 3 [] [] [Box "pair" [1, 0] [2], Box "anchor" [] [0]] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> expect "no rewrite" 0 (length (rewrites r host))
    , testProperty "replacement creates fresh internal nodes" $ do
        let gate = diagram 2 [0] [1] [Box "doubleNot" [0] [1]] :: Open ~> Open
        case rule gate chain of
          Left err -> testFailed err
          Right r ->
            expectOnly
              (diagram 3 [] [] [Box "not" [0] [1], Box "not" [1] [2]])
              (rewrites r (diagram 2 [] [] [Box "doubleNot" [0] [1]] :: Closed ~> Closed))
    , testProperty "identical box occurrences produce distinct matches" $ do
        let gate = diagram 2 [0] [1] [Box "not" [0] [1]] :: Open ~> Open
        case rule gate wire of
          Left err -> testFailed err
          Right r -> do
            let results = rewrites r (diagram 2 [] [] [Box "not" [0] [1], Box "not" [0] [1]] :: Closed ~> Closed)
                expected = diagram 1 [] [] [Box "not" [0] [0]] :: Closed ~> Closed
            expect "two occurrences" 2 (length results)
            check "wrong remaining box" (all (isomorphic expected) results)
    , batchTests
    , compiledTests
    , normalisationTests
    , testProperty "node numbering and box order do not affect cancellation" $
        withCancellation $ \r -> do
          let expected = diagram 2 [] [] [Box "source" [] [0], Box "sink" [0] []] :: Closed ~> Closed
              boxes = [Box "source" [] [0], Box "not" [0] [1], Box "not" [1] [2], Box "sink" [2] []]
              hosts =
                [ diagram 4 [] [] (map (fmap (renaming !!)) bs) :: Closed ~> Closed
                | renaming <- permutations [0 .. 3]
                , bs <- [boxes, reverse boxes]
                ]
          mapM_ (expectOnly expected . rewrites r) hosts
    ]

subgraphTests :: TestTree
subgraphTests =
  testGroup
    "Whole-arrow captures"
    [ testProperty "a composite region is retained inside its surrounding context" $ do
        r <- either testFailed pure (R.subgraphRule classify pattern' (linear ["$f"]))
        let results = rewrites r (linear ["before", "open", "a", "b", "close", "after"])
        expect "one anchored match" 1 (length results)
        check "context or captured composition changed" (all (isomorphic (linear ["before", "a", "b", "after"])) results)
    , testProperty "identity captures join endpoints without identifying unrelated nodes" $ do
        r <- either testFailed pure (R.subgraphRule classify pattern' (linear ["$f"]))
        check "identity capture failed" (case rewrites r (linear ["open", "close"]) of [g] -> isomorphic wire g; _ -> False)
        let malformed = diagram 2 [0] [1] [Box "open" [0] [0], Box "close" [0] [1]] :: Open ~> Open
        expect "unrelated nodes identified" 0 (length (rewrites r malformed))
    , testProperty "repeated captures compare whole regions up to internal renaming" $ do
        r <-
          either testFailed pure (R.subgraphRule classify (linear ["open", "$f", "separator", "$f", "close"]) (linear ["$f"]))
        let equal = linear ["open", "a", "b", "separator", "a", "b", "close"]
            unequal = linear ["open", "a", "b", "separator", "a", "c", "close"]
        check "equal regions rejected" (case rewrites r equal of [g] -> isomorphic (linear ["a", "b"]) g; _ -> False)
        expect "unequal regions accepted" 0 (length (rewrites r unequal))
    , testProperty "copying allocates distinct internal nodes and counts captured boxes" $ do
        r <- either testFailed pure (R.subgraphRule classify pattern' (linear ["$f", "$f"]))
        let host = linear ["open", "a", "b", "close"]
        check
          "copies share internal nodes"
          (case rewrites r host of [g] -> isomorphic (linear ["a", "b", "a", "b"]) g; _ -> False)
        compiled <- either testFailed pure (compileReducingRules [((), r)])
        expect "equal-size copying accepted as a reduction" 0 (length (rewritesCompiled compiled host))
    , testProperty "discarding a capture cannot cut an external connection" $ do
        r <- either testFailed pure (R.subgraphRule classify pattern' (linear []))
        check "discarding failed" (case rewrites r (linear ["open", "a", "b", "close"]) of [g] -> isomorphic wire g; _ -> False)
        let leaking =
              diagram 5 [0] [4] [Box "open" [0] [1], Box "a" [1] [2], Box "b" [2] [3], Box "close" [3] [4], Box "tap" [2] [0]]
                :: Open ~> Open
        expect "external connection was captured" 0 (length (rewrites r leaking))
    , testProperty "compatible matches account for captured boxes when batching" $ do
        r <- either testFailed pure (R.subgraphRule classify pattern' (linear ["$f"]))
        let (count, result) = rewriteBatch r (linear ["open", "a", "close", "open", "b", "close"])
        expect "two disjoint regions" 2 count
        check "batch changed captured bodies" (isomorphic (linear ["a", "b"]) result)
    , testProperty "an unanchored identity is not expanded" $ do
        r <- either testFailed pure (R.subgraphRule classify (linear ["$f"]) (linear ["done"]))
        expect "identity expanded" 0 (length (rewrites r wire))
    ]
  where
    linear labels = diagram (length labels + 1) [0] [length labels] [Box l [i] [i + 1] | (i, l) <- zip [0 ..] labels] :: Open ~> Open
    classify ('$' : name) = Right name
    classify l = Left l
    pattern' = linear ["open", "$f", "close"]

reducingTests :: TestTree
reducingTests =
  testGroup
    "Decreasing box count"
    [ testProperty "growth and self-loops cannot block a competing reduction" $ do
        let gate = diagram 2 [0] [1] [Box "not" [0] [1]] :: Open ~> Open
        grow <- either testFailed pure (rule gate chain)
        loop <- either testFailed pure (rule chain chain)
        cancel <- either testFailed pure (rule chain wire)
        let rules = [(0 :: Int, grow), (1, loop), (2, cancel)]
        ordinary <- either testFailed pure (compileRules rules)
        reducing <- either testFailed pure (compileReducingRules rules)
        expect "ordinary rewriting retains every candidate" [0, 0, 1, 2] (map fst (rewritesCompiled ordinary chain))
        expect "only cancellation decreases" [2] (map fst (rewritesCompiled reducing chain))
        let (count, result) = rewriteBatchCompiled reducing chain
        expect "shrinking match not blocked" 1 count
        check "cancellation changed" (isomorphic wire result)
        let normal = normalise unlimitedRewrites reducing chain
        expect "normal form" NormalForm (normalisationStatus normal)
        expect "one application" 1 (normalisationRewrites normal)
        check "normalisation changed" (isomorphic wire (normalisedGraph normal))
    , testProperty "dynamic replacement sizes are checked independently per match" $ do
        let lhs =
              R.PortGraph @()
                []
                []
                [Box (Phase "old" (Variable "a")) [] [R.Capture "legs"], Box (Marker "token") [] []]
            build sizes =
              R.PortGraph
                []
                []
                (replicate (sizes M.! "legs") (Box (Phase "new" (Variable "a")) [] [R.Capture "legs"]))
        r <- either testFailed pure (R.parameterPortRuleWith lhs build)
        compiled <- either testFailed pure (compileReducingRules [((), r)])
        mapM_
          ( \n -> do
              let host = pdiagram n [] [] [Box (Phase "old" 7) [] [0 .. n - 1], Box (Marker "token") [] []] :: PClosed Int ~> PClosed Int
                  results = rewritesCompiled compiled host
              expect "only smaller replacements apply" (if n < 2 then 1 else 0) (length results)
              check
                "wrong instantiated replacement"
                (all (\(_, g) -> isomorphic (pdiagram n [] [] (replicate n (Box (Phase "new" 7) [] [0 .. n - 1]))) g) results)
          )
          [0 .. 3]
    ]

normalisationTests :: TestTree
normalisationTests =
  testGroup
    "Normalisation"
    [ testProperty "unrestricted normalisation agrees with repeated single-rule batches" $
        withCancellation $ \r -> do
          n <- Falsify.gen (Gen.elem (0 :| [1 .. 10]))
          let host = diagram (n + 1) [0] [n] [Box "not" [i] [i + 1] | i <- [0 .. n - 1]] :: Open ~> Open
              reference total passes g = case rewriteBatch r g of
                (0, _) -> (total, passes, g)
                (count, next) -> reference (total + fromIntegral count) (passes + 1) next
              (steps, batches, expected) = reference 0 0 host
          withRules [(0 :: Int, r)] $ \compiled ->
            checkResult (normalise unlimitedRewrites compiled host) NormalForm steps batches expected
    , testProperty "a rewrite limit truncates a batch and the result can be resumed" $
        withErase $ \compiled -> do
          let result = normalise (unlimitedRewrites{maxRewrites = Just 2}) compiled threeGates
          checkResult result RewriteLimitReached 2 1 oneGate
          checkResult
            (normalise (unlimitedRewrites{maxRewrites = Just 1}) compiled (normalisedGraph result))
            NormalForm
            1
            1
            wire
    , testProperty "an exact rewrite budget reports normal form" $
        withErase $ \compiled ->
          checkResult (normalise (unlimitedRewrites{maxRewrites = Just 3}) compiled threeGates) NormalForm 3 1 wire
    , testProperty "limits larger than Int do not overflow" $
        withErase $ \compiled ->
          checkResult
            (normalise (unlimitedRewrites{maxRewrites = Just (fromIntegral (maxBound :: Int) + 1)}) compiled threeGates)
            NormalForm
            3
            1
            wire
    , testProperty "a batch limit stops before newly enabled matches" $
        withPhases $ \compiled -> do
          let result = normalise (unlimitedRewrites{maxBatches = Just 1}) compiled phaseA
          checkResult result BatchLimitReached 2 1 phaseB
          checkResult
            (normalise (unlimitedRewrites{maxBatches = Just 1}) compiled (normalisedGraph result))
            NormalForm
            2
            1
            wire
    , testProperty "a rewrite limit also truncates a later batch" $
        withPhases $ \compiled ->
          checkResult
            (normalise (RewriteLimits (Just 3) (Just 2)) compiled phaseA)
            RewriteLimitReached
            3
            2
            (gate "b")
    , testProperty "zero budgets do not apply a rule" $
        withErase $ \compiled -> do
          checkResult (normalise (unlimitedRewrites{maxRewrites = Just 0}) compiled threeGates) RewriteLimitReached 0 0 threeGates
          checkResult (normalise (unlimitedRewrites{maxBatches = Just 0}) compiled threeGates) BatchLimitReached 0 0 threeGates
          checkResult (normalise (RewriteLimits (Just 0) (Just 0)) compiled threeGates) RewriteLimitReached 0 0 threeGates
    , testProperty "a normal form needs no budget, including with an empty rule set" $
        withErase $ \compiled -> do
          checkResult (normalise (RewriteLimits (Just 0) (Just 0)) compiled wire) NormalForm 0 0 wire
          withRules ([] :: [(Int, Rule (MatK Int) String)]) $ \empty ->
            checkResult (normalise (RewriteLimits (Just 0) (Just 0)) empty threeGates) NormalForm 0 0 threeGates
    , testProperty "cyclic rule sets stop at either limit" $
        withRule (gate "a") (gate "b") $ \ab ->
          withRule (gate "b") (gate "a") $ \ba ->
            withRules [(0 :: Int, ab), (1, ba)] $ \compiled -> do
              checkResult (normalise (unlimitedRewrites{maxRewrites = Just 3}) compiled (gate "a")) RewriteLimitReached 3 3 (gate "b")
              checkResult (normalise (unlimitedRewrites{maxBatches = Just 2}) compiled (gate "a")) BatchLimitReached 2 2 (gate "a")
    , testProperty "graph equality does not stop an applicable self-rewrite" $
        withRule (gate "a") (gate "a") $ \r ->
          withRules [(0 :: Int, r)] $ \compiled ->
            checkResult (normalise (unlimitedRewrites{maxRewrites = Just 2}) compiled (gate "a")) RewriteLimitReached 2 2 (gate "a")
    , testProperty "limits also stop rules with empty left sides" $ do
        let empty = diagram 0 [] [] [] :: Closed ~> Closed
            scalar = diagram 0 [] [] [Box "scalar" [] []] :: Closed ~> Closed
            expected = diagram 0 [] [] (replicate 2 (Box "scalar" [] [])) :: Closed ~> Closed
        withRule empty scalar $ \r ->
          withRules [(0 :: Int, r)] $ \compiled ->
            checkResult (normalise (unlimitedRewrites{maxRewrites = Just 2}) compiled empty) RewriteLimitReached 2 2 expected
    ]
  where
    gate name = diagram 2 [0] [1] [Box name [0] [1]] :: Open ~> Open
    threeGates = diagram 4 [0] [3] [Box "erase" [0] [i] | i <- [1 .. 3]] :: Open ~> Open
    oneGate = gate "erase"
    phase name = diagram 3 [0] [2] [Box name [0] [1], Box name [1] [2]] :: Open ~> Open
    phaseA = phase "a"
    phaseB = phase "b"
    withRule lhs rhs k = either testFailed k (rule lhs rhs)
    withRules entries k = either testFailed k (compileRules entries)
    withErase k = withRule (gate "erase") wire $ \r -> withRules [(0 :: Int, r)] k
    withPhases k = withRule (gate "a") (gate "b") $ \ab ->
      withRule (gate "b") wire $ \erase -> withRules [(0 :: Int, ab), (1, erase)] k
    checkResult result status steps batches expected = do
      expect "stopping reason" status (normalisationStatus result)
      expect "rewrite count" steps (normalisationRewrites result)
      expect "batch count" batches (normalisationBatches result)
      check "resulting graph" (isomorphic expected (normalisedGraph result))

compiledTests :: TestTree
compiledTests =
  testGroup
    "Compiled rules"
    [ testProperty "generated patterns agree with independent matching and batching" $ do
        count <- Falsify.gen (Gen.elem (0 :| [1 .. 3]))
        lhsBoxes <- replicateM count (genBox 3)
        hostCount <- Falsify.gen (Gen.elem (0 :| [1 .. 6]))
        hostBoxes <- replicateM hostCount (genBox 4)
        let lhs = diagram 3 [0, 1, 2] [] lhsBoxes :: (Wires '[M Nat2, M Nat2, M Nat2] :: OH) ~> Wires '[]
            rhs = diagram 3 [0, 1, 2] [] [Box "done" [0, 1, 2] []] :: (Wires '[M Nat2, M Nat2, M Nat2] :: OH) ~> Wires '[]
            host = diagram 4 [] [] hostBoxes :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            agree [(0 :: Int, r)] host
            case compileRules [(0 :: Int, r)] of
              Left err -> testFailed err
              Right compiled -> do
                let (oldCount, oldResult) = rewriteBatch r host
                    (count', result) = rewriteBatchCompiled compiled host
                expect "same maximal batch size" oldCount count'
                check "same batch result" (isomorphic oldResult result)
    , testProperty "multiple patterns retain duplicates, dangling checks, and match order" $
        withCancellation $ \cancel -> do
          let repeated = diagram 2 [0] [1] [Box "repeat" [0] [1, 1]] :: Open ~> Open
              scalar = diagram 0 [] [] [Box "scalar" [] []] :: Closed ~> Closed
              isolated = diagram 1 [] [] [] :: Closed ~> Closed
              disconnected = diagram 4 [] [] [Box "a" [0] [1], Box "b" [2] [3]] :: Closed ~> Closed
              empty = diagram 0 [] [] [] :: Closed ~> Closed
          case (rule repeated wire, rule scalar empty, rule isolated empty, rule disconnected empty) of
            (Right repeatRule, Right scalarRule, Right isolatedRule, Right disconnectedRule) -> do
              size <- Falsify.gen (Gen.elem (0 :| [1 .. 7]))
              boxes <- replicateM size (genBox 4)
              let entries = [(4, cancel), (0, repeatRule), (3, scalarRule), (1, isolatedRule), (2 :: Int, disconnectedRule), (5, cancel)]
                  host = diagram 4 [] [] boxes :: Closed ~> Closed
              agree entries host
              agree (reverse entries) host
              agree
                entries
                (diagram 5 [] [] [Box "not" [0] [1], Box "not" [1] [2], Box "repeat" [0] [3, 3], Box "scalar" [] []] :: Closed ~> Closed)
              agree entries (diagram 5 [] [] [Box "not" [0] [1], Box "not" [1] [2], Box "tap" [1] []] :: Closed ~> Closed)
              agree [(0 :: Int, cancel)] (diagram 3 [1] [2] [Box "not" [0] [1], Box "not" [1] [2]] :: Open ~> Open)
              agree
                [(0 :: Int, cancel)]
                (diagram 3 [0, 0] [2] [Box "not" [0] [1], Box "not" [1] [2]] :: (Wires '[M Nat2, M Nat2] :: OH) ~> Open)
            _ -> testFailed "invalid test rules"
    , testProperty "shared dispatch respects sorts" $ do
        let lhs sorts = unsafeOpenHypergraph sorts [] [] [Box "gate" [0] [1]] :: Closed ~> Closed
            empty = diagram 0 [] [] [] :: Closed ~> Closed
            host =
              unsafeOpenHypergraph (sortList @_ @'[M Nat2, M Nat2, M Nat3, M Nat3]) [] [] [Box "gate" [0] [1], Box "gate" [2] [3]]
                :: Closed ~> Closed
        case (rule (lhs (sortList @_ @'[M Nat2, M Nat2])) empty, rule (lhs (sortList @_ @'[M Nat3, M Nat3])) empty) of
          (Right a, Right b) -> agree [(0 :: Int, a), (1, b)] host
          _ -> testFailed "invalid sorted rules"
    , testProperty "different rules share a batch with fresh replacement nodes" $ do
        let expand = diagram 2 [0] [1] [Box "expand" [0] [1]] :: Open ~> Open
            erase = diagram 2 [0] [1] [Box "erase" [0] [1]] :: Open ~> Open
            host = diagram 3 [] [] [Box "expand" [0] [1], Box "erase" [0] [2]] :: Closed ~> Closed
            expected = diagram 3 [] [] [Box "not" [0] [2], Box "not" [2] [1]] :: Closed ~> Closed
        case (rule expand chain, rule erase wire) of
          (Right a, Right b) -> mapM_ (batchIs host 2 expected) (permutations [(0 :: Int, a), (1, b)])
          _ -> testFailed "invalid batch rules"
    , testProperty "conflict priority is explicit and independent of rule-list order" $ do
        let lhs = diagram 2 [0] [1] [Box "gate" [0] [1]] :: Open ~> Open
            low = diagram 2 [0] [1] [Box "low" [0] [1]] :: Open ~> Open
            high = diagram 2 [0] [1] [Box "high" [0] [1]] :: Open ~> Open
        case (rule lhs low, rule lhs high) of
          (Right a, Right b) -> mapM_ (batchIs lhs 1 low) (permutations [(10 :: Int, a), (20, b)])
          _ -> testFailed "invalid priority rules"
    , testProperty "cross-rule deletions protect other matches' read nodes" $ do
        let isolated = diagram 1 [] [] [] :: Closed ~> Closed
            empty = diagram 0 [] [] [] :: Closed ~> Closed
            readNode = diagram 1 [0] [] [] :: Open ~> (Wires '[] :: OH)
            tagNode = diagram 1 [0] [] [Box "tag" [0] []] :: Open ~> (Wires '[] :: OH)
            host = diagram 2 [] [] [] :: Closed ~> Closed
            expected = diagram 2 [] [] [Box "tag" [0] [], Box "tag" [1] []] :: Closed ~> Closed
        case (rule isolated empty, rule readNode tagNode) of
          (Right remove, Right tag) -> batchIs host 2 expected [(1 :: Int, remove), (0, tag)]
          _ -> testFailed "invalid node rules"
    , testProperty "empty rule sets leave the host unchanged" $ do
        let host = diagram 1 [] [] [] :: Closed ~> Closed
        batchIs host 0 host ([] :: [(Int, Rule (MatK Int) String)])
        agree ([] :: [(Int, Rule (MatK Int) String)]) host
    , testProperty "an empty pattern has one match" $ do
        let empty = diagram 0 [] [] [] :: Closed ~> Closed
            host = diagram 1 [] [] [Box "loop" [0] [0]] :: Closed ~> Closed
        case rule empty empty of
          Left err -> testFailed err
          Right r -> do
            agree [(0 :: Int, r)] host
            batchIs host 1 host [(0 :: Int, r)]
    , testProperty "duplicate keys are rejected" $
        withCancellation $
          \r -> check "accepted duplicate keys" (isLeft (compileRules [(0 :: Int, r), (0, r)]))
    ]
  where
    genBox nodes = do
      label <- Falsify.gen (Gen.elem ("not" :| ["repeat", "a", "b", "scalar"]))
      ins <- Falsify.gen (Gen.elem (0 :| [1, 2]))
      outs <- Falsify.gen (Gen.elem (0 :| [1, 2]))
      let node = Falsify.gen (Gen.elem (0 :| [1 .. nodes - 1]))
      Box label <$> replicateM ins node <*> replicateM outs node
    agree entries host = case compileRules entries of
      Left err -> testFailed err
      Right compiled -> do
        let expected = [(key, g) | (key, r) <- sortOn fst entries, g <- rewrites r host]
            actual = rewritesCompiled compiled host
        expect "rule keys and match multiplicity" (map fst expected) (map fst actual)
        check "results or enumeration order differ" (and (zipWith (\(_, a) (_, b) -> isomorphic a b) expected actual))
    batchIs host count expected entries = case compileRules entries of
      Left err -> testFailed err
      Right compiled -> do
        let (actualCount, actual) = rewriteBatchCompiled compiled host
        expect "batch count" count actualCount
        check "batch result" (isomorphic expected actual)

batchTests :: TestTree
batchTests =
  testGroup
    "Batches"
    [ testProperty "adjacent cancellations share a preserved interface" $
        withCancellation $ \r -> do
          let host = diagram 5 [0] [4] [Box "not" [i] [i + 1] | i <- [0 .. 3]] :: Open ~> Open
              (count, result) = rewriteBatch r host
          expect "two disjoint pairs" 2 count
          check "not an identity wire" (isomorphic wire result)
          case rewrites r host of
            first : _ -> case rewrites r first of
              second : _ -> check "batch differs from sequential cancellation" (isomorphic second result)
              [] -> testFailed "missing second sequential step"
            [] -> testFailed "missing first sequential step"
    , testProperty "parallel matches can share their input node" $ do
        let lhs = diagram 2 [0] [1] [Box "not" [0] [1]] :: Open ~> Open
            rhs = diagram 2 [0] [1] [Box "done" [0] [1]] :: Open ~> Open
            host = diagram 3 [] [] [Box "not" [0] [1], Box "not" [0] [2]] :: Closed ~> Closed
            expected = diagram 3 [] [] [Box "done" [0] [1], Box "done" [0] [2]] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            let (count, result) = rewriteBatch r host
            expect "both branches" 2 count
            check "wrong replacements" (isomorphic expected result)
    , testProperty "replacement internal nodes are fresh for each match" $ do
        let lhs = diagram 2 [0] [1] [Box "expand" [0] [1]] :: Open ~> Open
            host = diagram 3 [] [] [Box "expand" [0] [1], Box "expand" [0] [2]] :: Closed ~> Closed
            expected = diagram 5 [] [] [Box "not" [0] [3], Box "not" [3] [1], Box "not" [0] [4], Box "not" [4] [2]] :: Closed ~> Closed
        case rule lhs chain of
          Left err -> testFailed err
          Right r -> do
            let (count, result) = rewriteBatch r host
            expect "two expansions" 2 count
            check "replacement nodes were shared" (isomorphic expected result)
    , testProperty "isolated-node deletions protect other matches' read nodes" $ do
        let lhs = diagram 2 [0] [] [] :: Open ~> (Wires '[] :: OH)
            rhs = diagram 1 [0] [] [] :: Open ~> (Wires '[] :: OH)
            host = diagram 3 [] [] [] :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            let (count, result) = rewriteBatch r host
            expect "one preserved node, two deletions" 2 count
            check "preserved node was lost" (isomorphic (diagram 1 [] [] []) result)
    , testProperty "nullary boxes can be deleted together" $ do
        let lhs = diagram 0 [] [] [Box "scalar" [] []] :: Closed ~> Closed
            rhs = diagram 0 [] [] [] :: Closed ~> Closed
            host = diagram 1 [] [] (replicate 3 (Box "scalar" [] [])) :: Closed ~> Closed
        case rule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            let (count, result) = rewriteBatch r host
            expect "three scalars" 3 count
            check "isolated host node changed" (isomorphic (diagram 1 [] [] []) result)
    , testProperty "new matches are left for another batch" $ do
        let lhs = diagram 2 [0] [1] [Box "not" [0] [1]] :: Open ~> Open
        case rule lhs chain of
          Left err -> testFailed err
          Right r -> do
            let (count, result) = rewriteBatch r lhs
            expect "only the snapshot occurrence" 1 count
            check "expansion was reapplied" (isomorphic chain result)
    , testProperty "no matches returns the unchanged host" $
        withCancellation $ \r -> do
          let host = diagram 2 [] [] [Box "other" [0] [1]] :: Closed ~> Closed
              (count, result) = rewriteBatch r host
          expect "no applications" 0 count
          check "host changed" (isomorphic host result)
    ]

-- Label structure and fixed fields stay literal; traversed fields bind values.
data PLabel a = Phase String a | Pair a a | Marker String
  deriving (Eq, Show, Functor, Foldable, Traversable)

type PGraph a = OPENHG () (PLabel a)
type POpen a = Wires W1 :: PGraph a
type PClosed a = Wires '[] :: PGraph a

pdiagram
  :: (SortList as, SortList bs)
  => Int -> [Int] -> [Int] -> [Box (PLabel a) Int] -> (Wires as :: PGraph a) ~> Wires bs
pdiagram n = unsafeOpenHypergraph (concat (replicate n (sortList @() @W1)))

pchain :: a -> a -> POpen a ~> POpen a
pchain a b = pdiagram 3 [0] [2] [Box (Phase "z" a) [0] [1], Box (Phase "z" b) [1] [2]]

pgate :: PLabel a -> POpen a ~> POpen a
pgate label = pdiagram 2 [0] [1] [Box label [0] [1]]

withParameterRule :: Either String (Rule () (PLabel Int)) -> (Rule () (PLabel Int) -> Property ()) -> Property ()
withParameterRule candidate k = either testFailed k candidate

parameterTests :: TestTree
parameterTests =
  testGroup
    "parameters"
    [ testProperty "one compiled rule computes replacements for unseen values" $
        withParameterRule
          (parameterRule (pchain (Variable "a") (Variable "b")) (pgate (Phase "z" (Variable "a" - Variable "b"))))
          \r -> do
            a <- Falsify.gen (Gen.elem ((-17) :| [0, 1, 7, 12345]))
            b <- Falsify.gen (Gen.elem ((-29) :| [0, 2, 11, 67890]))
            let host = pchain a b
                expected = pgate (Phase "z" (a - b))
            check "uncompiled substitution" (case rewrites r host of [g] -> isomorphic expected g; _ -> False)
            case compileRules [(0 :: Int, r)] of
              Left err -> testFailed err
              Right compiled -> do
                check "compiled substitution" (case rewritesCompiled compiled host of [(0, g)] -> isomorphic expected g; _ -> False)
                let result = normalise unlimitedRewrites compiled (pchain a b)
                expect "normal form" NormalForm (normalisationStatus result)
                expect "one application" 1 (normalisationRewrites result)
                check "computed result" (isomorphic expected (normalisedGraph result))
    , testProperty "normalisation reuses compiled parameter rules for newly computed values" $
        withParameterRule
          (parameterRule (pchain (Variable "a") (Variable "b")) (pgate (Phase "z" (Variable "a" + Variable "b"))))
          \fusion -> do
            let wireP = pdiagram 1 [0] [0] [] :: POpen Int ~> POpen Int
                host =
                  pdiagram 4 [0] [3] [Box (Phase "z" 2) [0] [1], Box (Phase "z" 3) [1] [2], Box (Phase "z" (-5)) [2] [3]]
                    :: POpen Int ~> POpen Int
            case rule (pgate (Phase "z" 0)) wireP >>= \identity -> compileRules [(0 :: Int, identity), (1, fusion)] of
              Left err -> testFailed err
              Right compiled -> do
                let result = normalise unlimitedRewrites compiled host
                expect "two fusions and identity removal" 3 (normalisationRewrites result)
                expect "normal form" NormalForm (normalisationStatus result)
                check "phases did not cancel" (isomorphic wireP (normalisedGraph result))
    , testProperty "repeated variables enforce equality across labels" $
        withParameterRule (parameterRule (pchain (Variable "a") (Variable "a")) (pgate (Phase "z" (2 * Variable "a")))) \r -> do
          expect "unequal parameters" 0 (length (rewrites r (pchain 3 4)))
          check "equal parameters" (case rewrites r (pchain 7 7) of [g] -> isomorphic (pgate (Phase "z" 14)) g; _ -> False)
          case compileRules [(0 :: Int, r)] of
            Left err -> testFailed err
            Right compiled -> expect "compiled equality check" 0 (length (rewritesCompiled compiled (pchain 3 4)))
    , testProperty "literals, repeated fields, constructors and fixed label fields constrain matches" $
        withParameterRule (parameterRule (pgate (Pair (Variable "a") (Variable "a"))) (pgate (Phase "answer" (Variable "a")))) \r -> do
          expect "different fields" 0 (length (rewrites r (pgate (Pair 3 4))))
          expect "different constructor" 0 (length (rewrites r (pgate (Phase "z" 3))))
          check "same fields" (case rewrites r (pgate (Pair 8 8)) of [g] -> isomorphic (pgate (Phase "answer" 8)) g; _ -> False)
          withParameterRule (parameterRule (pchain (Literal 3) (Variable "b")) (pgate (Phase "z" (Variable "b")))) \literal -> do
            expect "literal mismatch" 0 (length (rewrites literal (pchain 4 5)))
            let wrongColour = pdiagram 3 [0] [2] [Box (Phase "x" 3) [0] [1], Box (Phase "z" 5) [1] [2]] :: POpen Int ~> POpen Int
            expect "fixed field mismatch" 0 (length (rewrites literal wrongColour))
    , testProperty "parameter values follow pattern order when compilation anchors a later box" $ do
        let lhs =
              pdiagram 3 [0] [2] [Box (Phase "z" (Variable "a")) [0] [1], Box (Pair (Variable "b") (Literal 9)) [1, 1] [2]]
                :: POpen (Parameter Int) ~> POpen (Parameter Int)
            rhs = pgate (Phase "result" (Variable "a" - Variable "b"))
            host = pdiagram 3 [0] [2] [Box (Phase "z" 7) [0] [1], Box (Pair 2 9) [1, 1] [2]] :: POpen Int ~> POpen Int
        withParameterRule (parameterRule lhs rhs) \r ->
          case compileRules [(0 :: Int, r)] of
            Left err -> testFailed err
            Right compiled ->
              check
                "bindings were reordered"
                (case rewritesCompiled compiled host of [(0, g)] -> isomorphic (pgate (Phase "result" 5)) g; _ -> False)
    , testProperty "bindings are fresh for each match in one batch" $
        withParameterRule
          (parameterRule (pchain (Variable "a") (Variable "b")) (pgate (Phase "z" (Variable "a" + Variable "b"))))
          \r -> do
            let host =
                  pdiagram
                    6
                    []
                    []
                    [Box (Phase "z" 2) [0] [1], Box (Phase "z" 3) [1] [2], Box (Phase "z" 11) [3] [4], Box (Phase "z" 17) [4] [5]]
                    :: PClosed Int ~> PClosed Int
                expected = pdiagram 4 [] [] [Box (Phase "z" 5) [0] [1], Box (Phase "z" 28) [2] [3]] :: PClosed Int ~> PClosed Int
                (count, result) = rewriteBatch r host
            expect "two uncompiled matches" 2 count
            check "independent substitutions" (isomorphic expected result)
            case compileRules [(0 :: Int, r)] of
              Left err -> testFailed err
              Right compiled -> do
                let (n, g) = rewriteBatchCompiled compiled host
                expect "two compiled matches" 2 n
                check "independent compiled substitutions" (isomorphic expected g)
    , testProperty "a rejected binding does not block a lower-priority literal rule" $
        withParameterRule (parameterRule (pchain (Variable "a") (Variable "a")) (pgate (Phase "z" (Variable "a")))) \param -> do
          let host = pchain 3 4
              expected = pgate (Phase "z" 7)
          case rule host expected >>= \literal -> compileRules [(0 :: Int, param), (1, literal)] of
            Left err -> testFailed err
            Right compiled -> do
              let (n, g) = rewriteBatchCompiled compiled host
              expect "literal rule applies" 1 n
              check "right replacement" (isomorphic expected g)
              expect "only literal key" [1] (map fst (rewritesCompiled compiled host))
    , testProperty "shared parameter-pattern prefixes keep rule bindings separate" $
        withParameterRule (parameterRule (pchain (Variable "a") (Variable "a")) (pgate (Phase "equal" (Variable "a")))) \equal ->
          withParameterRule
            (parameterRule (pchain (Variable "a") (Variable "b")) (pgate (Phase "different" (Variable "a" - Variable "b"))))
            \general ->
              case compileRules [(0 :: Int, equal), (1, general)] of
                Left err -> testFailed err
                Right compiled -> do
                  expect "unequal values only match the general rule" [1] (map fst (rewritesCompiled compiled (pchain 3 4)))
                  expect "equal values match both rules" [0, 1] (map fst (rewritesCompiled compiled (pchain 3 3)))
                  let (n, result) = rewriteBatchCompiled compiled (pchain 3 4)
                  expect "one replacement" 1 n
                  check "wrong bindings" (isomorphic (pgate (Phase "different" (-1))) result)
    , testProperty "exact and constructor dispatch can both select the same host box" $
        withParameterRule (parameterRule (pgate (Phase "z" (Variable "a"))) (pgate (Phase "param" (Variable "a")))) \param ->
          case rule (pgate (Phase "z" 3)) (pgate (Phase "literal" 3)) >>= \literal -> compileRules [(1 :: Int, literal), (0, param)] of
            Left err -> testFailed err
            Right compiled -> expect "both keys" [0, 1] (map fst (rewritesCompiled compiled (pgate (Phase "z" 3))))
    , testProperty "compiled parameters agree with the exhaustive matcher on generated graphs" $
        withParameterRule
          ( parameterRule
              (pchain (Variable "a") (Variable "b"))
              (pgate (Phase "z" (mapParameter (`mod` 7) (Variable "a" + Variable "b"))))
          )
          \r -> do
            size <- Falsify.gen (Gen.elem (0 :| [1 .. 6]))
            boxes <- replicateM size $ do
              a <- Falsify.gen (Gen.elem (0 :| [1 .. 3]))
              b <- Falsify.gen (Gen.elem (0 :| [1 .. 3]))
              name <- Falsify.gen (Gen.elem ("z" :| ["x"]))
              value <- Falsify.gen (Gen.elem ((-1) :| [0, 1, 2, 3]))
              pure (Box (Phase name value) [a] [b])
            let host = pdiagram 4 [] [] boxes :: PClosed Int ~> PClosed Int
                expected = rewrites r host
            case compileRules [(0 :: Int, r)] of
              Left err -> testFailed err
              Right compiled -> do
                let actual = map snd (rewritesCompiled compiled host)
                expect "match multiplicity" (length expected) (length actual)
                check "match order and values" (and (zipWith isomorphic expected actual))
    , testProperty "parameter matching retains the dangling and injectivity checks" $
        withParameterRule
          (parameterRule (pchain (Variable "a") (Variable "b")) (pgate (Phase "z" (Variable "a" + Variable "b"))))
          \r -> do
            let tapped =
                  pdiagram 3 [] [] [Box (Phase "z" 1) [0] [1], Box (Phase "z" 2) [1] [2], Box (Marker "tap") [1] []]
                    :: PClosed Int ~> PClosed Int
                loop = pdiagram 2 [] [] [Box (Phase "z" 1) [0] [1], Box (Phase "z" 2) [1] [0]] :: PClosed Int ~> PClosed Int
            expect "dangling attachment" 0 (length (rewrites r tapped))
            expect "identified pattern nodes" 0 (length (rewrites r loop))
    , testProperty "invalid parameter rules fail before matching" $ do
        let a = Variable "a" :: Parameter Int
            b = Variable "b"
        check "unbound name accepted" (isLeft (parameterRule (pgate (Phase "z" a)) (pgate (Phase "z" b))))
        check "unbound name in expression accepted" (isLeft (parameterRule (pgate (Phase "z" a)) (pgate (Phase "z" (a + b)))))
        check "computed left expression accepted" (isLeft (parameterRule (pgate (Phase "z" (a + 1))) (pgate (Phase "z" a))))
        let wireP = pdiagram 1 [0] [0] [] :: POpen (Parameter Int) ~> POpen (Parameter Int)
        check "noninjective interface accepted" (isLeft (parameterRule wireP (pgate (Phase "z" (Literal 0)))))
    ]

portTests :: TestTree
portTests =
  testGroup
    "port captures"
    [ testProperty "one compiled rule captures arbitrary input/output arities and aliases" $ do
        let pg = R.PortGraph @() [] []
        case R.portRule (pg [Box "old" [R.Capture "in"] [R.Capture "out"]]) (pg [Box "new" [R.Capture "in"] [R.Capture "out"]]) >>= \r -> compileRules [(0 :: Int, r)] of
          Left err -> testFailed err
          Right compiled -> do
            ins <- Falsify.gen (Gen.elem ([] :| [[0], [0, 1], [1, 0, 1], [0, 0, 0, 1]]))
            outs <- Falsify.gen (Gen.elem ([] :| [[1], [1, 0], [0, 0, 1]]))
            let graph label =
                  unsafeOpenHypergraph (sortList @() @W2) [] [] [Box label ins outs]
                    :: (Wires '[] :: OPENHG () String) ~> Wires '[]
            check
              "capture changed ports"
              (case rewritesCompiled compiled (graph "old") of [(0, g)] -> isomorphic (graph "new") g; _ -> False)
    , testProperty "adjacent captures retain every split in order, including empty suffixes and aliases" $ do
        let pg = R.PortGraph @() [] []
            graph name ins outs =
              unsafeOpenHypergraph (sortList @() @W2) [] [] [Box name ins outs]
                :: (Wires '[] :: OPENHG () String) ~> Wires '[]
            lhs = pg [Box "old" [] [R.Capture "prefix", R.Capture "suffix"]]
            rhs = pg [Box "new" [R.Capture "prefix"] [R.Capture "suffix"]]
        case R.portRule lhs rhs >>= \r -> compileRules [(0 :: Int, r)] of
          Left err -> testFailed err
          Right compiled ->
            mapM_
              ( \ports -> do
                  let actual = map snd (rewritesCompiled compiled (graph "old" [] ports))
                      expected = [graph "new" (take n ports) (drop n ports) | n <- [0 .. length ports]]
                  expect "split count" (length expected) (length actual)
                  check "split order, empty capture or alias changed" (and (zipWith isomorphic expected actual))
              )
              [[], [0], [0, 1], [0, 1, 0]]
    , testProperty "a known port anchor retains every occurrence after a variable prefix" $ do
        let pg = R.PortGraph (sortList @() @W1) [0]
            lhs = pg [Box "old" [] [R.Capture "prefix", R.Node 0, R.Capture "suffix"], Box "anchor" [] [R.Node 0]]
            rhs = pg [Box "new" [R.Capture "prefix"] [R.Node 0, R.Capture "suffix"], Box "anchor" [] [R.Node 0]]
            graph name ins outs =
              unsafeOpenHypergraph (sortList @() @W2) [] [] [Box name ins outs, Box "anchor" [] [0]]
                :: (Wires '[] :: OPENHG () String) ~> Wires '[]
        case R.portRule lhs rhs >>= \r -> compileRules [(0 :: Int, r)] of
          Left err -> testFailed err
          Right compiled ->
            mapM_
              ( \ports -> do
                  let actual = map snd (rewritesCompiled compiled (graph "old" [] ports))
                      expected = [graph "new" (take n ports) (drop n ports) | (n, w) <- zip [0 ..] ports, w == 0]
                  expect "anchor occurrences" (length expected) (length actual)
                  check "anchor match order or captured suffix changed" (and (zipWith isomorphic expected actual))
              )
              [[], [1], [0], [1, 0, 1], [0, 1, 0]]
    , testProperty "captures preserve ordered sequences, including repeated names" $ do
        let pg = R.PortGraph @() [] []
            graph ins outs =
              unsafeOpenHypergraph (sortList @() @W2) [] [] [Box "old" ins outs]
                :: (Wires '[] :: OPENHG () String) ~> Wires '[]
        case R.portRule (pg [Box "old" [R.Capture "same"] [R.Capture "same"]]) (pg [Box "new" [] [R.Capture "same"]]) of
          Left err -> testFailed err
          Right r -> do
            expect "different order matched" 0 (length (rewrites r (graph [0, 1] [1, 0])))
            expect "different multiplicity matched" 0 (length (rewrites r (graph [0, 0] [0])))
            expect "same sequence did not match" 1 (length (rewrites r (graph [1, 0, 1] [1, 0, 1])))
    , testProperty "position-free incidence finds connections after variable prefixes" $ do
        let sorts2 = sortList @() @W1
            lhs =
              R.PortGraph
                sorts2
                []
                [Box "left" [] [R.Capture "a", R.Node 0, R.Capture "b"], Box "right" [] [R.Capture "c", R.Node 0, R.Capture "d"]]
            rhs = R.PortGraph [] [] [Box "joined" [] [R.Capture "a", R.Capture "b", R.Capture "c", R.Capture "d"]]
            graph boxes = unsafeOpenHypergraph (concat (replicate 5 sorts2)) [] [] boxes :: (Wires '[] :: OPENHG () String) ~> Wires '[]
            host = graph [Box "left" [] [1, 0, 2], Box "right" [] [3, 4, 0]]
            expected =
              unsafeOpenHypergraph (concat (replicate 4 sorts2)) [] [] [Box "joined" [] [0, 1, 2, 3]]
                :: (Wires '[] :: OPENHG () String) ~> Wires '[]
        case R.portRule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            check "connection or order lost" (case rewrites r host of [g] -> isomorphic expected g; _ -> False)
            expect
              "dangling connection was deleted"
              0
              (length (rewrites r (graph [Box "left" [] [1, 0, 2], Box "right" [] [3, 4, 0], Box "tap" [0] []])))
            let exposed =
                  unsafeOpenHypergraph (concat (replicate 5 sorts2)) [0] [] [Box "left" [] [1, 0, 2], Box "right" [] [3, 4, 0]]
                    :: (Wires W1 :: OPENHG () String) ~> Wires '[]
            expect "host boundary was deleted" 0 (length (rewrites r exposed))
    , testProperty "captured aliases of internal nodes cannot be deleted" $ do
        let ss = sortList @() @W1
            lhs = R.PortGraph ss [] [Box "old" [] [R.Node 0, R.Capture "rest"]]
            rhs = R.PortGraph [] [] [Box "new" [] [R.Capture "rest"]]
            graph = unsafeOpenHypergraph ss [] [] [Box "old" [] [0, 0]] :: (Wires '[] :: OPENHG () String) ~> Wires '[]
        case R.portRule lhs rhs of
          Left err -> testFailed err
          Right r -> expect "deleted a captured node" 0 (length (rewrites r graph))
    , testProperty "a capture can alias an explicit interface node" $ do
        let ss = sortList @() @W1
            lhs = R.PortGraph ss [0] [Box "old" [] [R.Node 0, R.Capture "rest"]]
            rhs = R.PortGraph ss [0] [Box "new" [] [R.Capture "rest", R.Node 0]]
            graph label = unsafeOpenHypergraph ss [0] [0] [Box label [] [0, 0]] :: (Wires W1 :: OPENHG () String) ~> Wires W1
        case R.portRule lhs rhs of
          Left err -> testFailed err
          Right r -> check "interface alias split" (case rewrites r (graph "old") of [g] -> isomorphic (graph "new") g; _ -> False)
    , testProperty "captured sorts are preserved and numbered-node sorts are checked" $ do
        let lhs = R.PortGraph (sortList @_ @'[M Nat2]) [0] [Box "old" [] [R.Capture "rest", R.Node 0]]
            rhs = R.PortGraph (sortList @_ @'[M Nat2]) [0] [Box "new" [] [R.Capture "rest", R.Node 0]]
            graph label = unsafeOpenHypergraph (sortList @_ @'[M Nat3, M Nat2]) [] [] [Box label [] [0, 1]] :: Closed ~> Closed
            wrong = unsafeOpenHypergraph (sortList @_ @'[M Nat2, M Nat3]) [] [] [Box "old" [] [0, 1]] :: Closed ~> Closed
        case R.portRule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            check "captured sort changed" (case rewrites r (graph "old") of [g] -> isomorphic (graph "new") g; _ -> False)
            expect "wrong numbered-node sort matched" 0 (length (rewrites r wrong))
    , testProperty "independent captured matches can share preserved nodes in one batch" $ do
        let pg = R.PortGraph @() [] []
            graph label =
              unsafeOpenHypergraph (sortList @() @W3) [] [] [Box label [] [0, 1], Box label [] [0, 2]]
                :: (Wires '[] :: OPENHG () String) ~> Wires '[]
        case R.portRule (pg [Box "old" [] [R.Capture "legs"]]) (pg [Box "new" [] [R.Capture "legs"]]) of
          Left err -> testFailed err
          Right r -> do
            let (n, result) = rewriteBatch r (graph "old")
            expect "both matches applied" 2 n
            check "sharing lost" (isomorphic (graph "new") result)
    , testProperty "a repeated binary connection can share one of its wires" $ do
        let sorts = concat (replicate 2 (sortList @() @W2))
            boundary = [0 .. 3]
            left = [R.Node 0, R.Capture "left", R.Node 2]
            right = [R.Node 1, R.Capture "right", R.Node 3]
            link a b = Box "link" [] [a, b]
            lhs =
              R.PortGraph
                sorts
                boundary
                [link (R.Node 0) (R.Node 1), Box "left" [] left, Box "right" [] right, link (R.Node 2) (R.Node 3)]
            rhs = R.PortGraph sorts boundary [Box "joined" [] (left ++ right)]
            graph boxes = unsafeOpenHypergraph sorts [] [] boxes :: (Wires '[] :: OPENHG () String) ~> Wires '[]
            path = [link 0 1, Box "left" [] [0, 2], Box "right" [] [1, 3]]
        r <- either testFailed pure (R.portRule lhs rhs)
        expect "one link cannot stand in for both fixed boxes" 0 (length (rewrites r (graph path)))
        mapM_
          ( \endpoint ->
              let shared = Box "shared" [] [endpoint]
              in case rewrites r (graph (path ++ [link 2 3, shared])) of
                   [target] -> check "either link may have another incidence" (isomorphic (graph [shared, Box "joined" [] [0, 2, 1, 3]]) target)
                   _ -> testFailed "expected one match using the shared wire"
          )
          [0, 2]
    , testProperty "length-dependent replacements allocate fresh nodes per captured occurrence" $ do
        let lhs = R.PortGraph @() [] [] [Box (Phase "old" (Variable "a")) [] [R.Capture "legs"]]
            build sizes =
              let n = sizes M.! "legs"
              in R.PortGraph
                   (concat (replicate n (sortList @() @W1)))
                   []
                   ( Box (Phase "new" (Variable "a" + 1)) [] [R.Node i | i <- [0 .. n - 1]]
                       : [Box (Marker "link") [R.Element "legs" i] [R.Node i] | i <- [0 .. n - 1]]
                   )
            host = pdiagram 1 [] [] [Box (Phase "old" 3) [] [0, 0], Box (Phase "old" 5) [] []] :: PClosed Int ~> PClosed Int
            expected =
              pdiagram
                3
                []
                []
                [Box (Phase "new" 4) [] [1, 2], Box (Marker "link") [0] [1], Box (Marker "link") [0] [2], Box (Phase "new" 6) [] []]
                :: PClosed Int ~> PClosed Int
        withParameterRule (R.parameterPortRuleWith lhs build) \r -> do
          let (n, result) = rewriteBatch r host
          expect "two replacements" 2 n
          check "fresh nodes or parameters mixed" (isomorphic expected result)
    , testProperty "literal and variable-arity signatures can both match a box" $ do
        let pg = R.PortGraph @() [] []
            graph label =
              unsafeOpenHypergraph (sortList @() @W2) [] [] [Box label [] [0, 1]]
                :: (Wires '[] :: OPENHG () String) ~> Wires '[]
        case R.portRule (pg [Box "old" [] [R.Capture "legs"]]) (pg [Box "variable" [] [R.Capture "legs"]]) >>= \variadic ->
          rule (graph "old") (graph "literal") >>= \literal -> compileRules [(1 :: Int, literal), (0, variadic)] of
          Left err -> testFailed err
          Right compiled -> expect "overlapping signatures lost" [0, 1] (map fst (rewritesCompiled compiled (graph "old")))
    , testProperty "invalid port templates fail at construction" $ do
        let ss = sortList @() @W1
            good = R.PortGraph ss [0] [Box "old" [] [R.Node 0, R.Capture "legs"]]
            rhs = R.PortGraph ss [0] [Box "new" [] [R.Capture "legs"]]
        check "bad left node" (isLeft (R.portRule (R.PortGraph ss [0] [Box "old" [] [R.Node 1]]) rhs))
        check "bad left interface" (isLeft (R.portRule (R.PortGraph ss [1] []) rhs))
        check "bad right node" (isLeft (R.portRule good (R.PortGraph ss [0] [Box "new" [] [R.Node 1]])))
        check "unbound capture" (isLeft (R.portRule good (R.PortGraph ss [0] [Box "new" [] [R.Capture "missing"]])))
        check "negative capture index" (isLeft (R.portRule good (R.PortGraph ss [0] [Box "new" [] [R.Element "legs" (-1)]])))
        check "Element on left" (isLeft (R.portRule (R.PortGraph ss [0] [Box "old" [] [R.Element "legs" 0]]) rhs))
        check
          "repeated left interface"
          (isLeft (R.portRule (R.PortGraph ss [0, 0] []) (R.PortGraph ss [0, 0] [] :: R.PortGraph () String)))
        let mismatched = R.PortGraph (sortList @_ @'[M Nat3]) [0] [] :: R.PortGraph (MatK Int) String
            left = R.PortGraph (sortList @_ @'[M Nat2]) [0] []
        check "wrong interface sort" (isLeft (R.portRule left mismatched))
    , testProperty "bad dynamic replacements reject the candidate before batch selection" $ do
        let lhs = R.PortGraph @() [] [] [Box (Phase "old" (Variable "a")) [] [R.Capture "legs"]]
            graph = pdiagram 1 [] [] [Box (Phase "old" 3) [] [0]] :: PClosed Int ~> PClosed Int
            builders =
              [ const (R.PortGraph [] [] [Box (Phase "bad" (Variable "a")) [] [R.Node 0]])
              , const (R.PortGraph [] [] [Box (Phase "bad" (Variable "a")) [] [R.Element "legs" 9]])
              , const (R.PortGraph [] [] [Box (Phase "bad" (Variable "missing")) [] []])
              , const (R.PortGraph [] [] [Box (Phase "bad" (Variable "a")) [] [R.Capture "missing"]])
              ]
        mapM_
          ( \build -> withParameterRule (R.parameterPortRuleWith lhs build) \r -> do
              expect "invalid candidate matched" 0 (length (rewrites r graph))
              case rule graph (pdiagram 1 [] [] [] :: PClosed Int ~> PClosed Int) >>= \fallback -> compileRules [(0 :: Int, r), (1, fallback)] of
                Left err -> testFailed err
                Right compiled -> expect "invalid replacement blocked fallback" [1] (map fst (rewritesCompiled compiled graph))
          )
          builders
    ]
