{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | Optimise an existing circuit through its gate-labelled hypergraph, then
-- simulate and emit Verilog through the reconstructed netlist.
module Examples.CircuitRewrite
  ( test
  , redundant
  , optimisedNetlist
  , optimise
  , optimiseWithStats
  , OptimisationStats (..)
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict qualified as IM
import Data.List (find, isInfixOf, sort)
import Data.List.NonEmpty (NonEmpty (..))
import Test.Falsify (Property, testFailed)
import Test.Falsify qualified as Falsify
import Test.Falsify.Generator qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Examples.Circuit (counter)
import Examples.CircuitRewrite.Workloads qualified as Workloads
import Proarrow.Category.Instance.Circuit
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.Simulator (runSimulator)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.CopyDiscard (discard, (&&&))
import Proarrow.Category.Monoidal.CopyDiscard qualified as Copy
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Functor qualified as F
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Testing (check, expect, genNamed)
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.SMC (SYN (..), returnA, toSMC, (-<))
import Proarrow.Tools.SMC qualified as SMC
import Props.Circuit ()

-- | Gate counts in the input and returned netlists, and successful rewrite steps.
data OptimisationStats = OptimisationStats
  { gatesBefore :: Int
  , gatesAfter :: Int
  , rewriteSteps :: Int
  }
  deriving (Eq, Show)

-- | Simplify a netlist using double negation, constant folding, and local Boolean
-- identities for NOT, AND, OR, XOR, and muxes. Binary identities cover both operand
-- orders, repeated inputs, and complementary inputs. Mux rules cover constant
-- selectors, equal branches, a selector reused as a branch, constant branch pairs,
-- @mux s True b = OR s b@, and @mux s a False = AND s a@.
-- A discrimination net matches the compiled rule set on one snapshot; a greedy
-- batch of compatible matches across rules is applied, then matching restarts.
-- Built-in rule priorities resolve conflicts. Each match decreases the total number
-- of gate input ports, so the pass terminates. Statistics count matches rather
-- than batches; replacing a gate with a constant need not reduce the gate count.
-- Rules preserve source and intermediate signals for other users. Unused gates
-- are pruned when the simplified graph is imported.
--
-- The input is validated before rewriting, so simplification cannot mask an
-- observable combinational cycle. The result is validated on import. Register
-- delays and initial values are unchanged. This is a local fixed point of these
-- rules, not a minimal circuit or a complete Boolean simplifier.
optimise
  :: forall a b
   . (KnownWires a, KnownWires b)
  => Netlist a b -> Either CircuitGraphError (Netlist a b)
optimise n = fst <$> optimiseWithStats n

-- | 'optimise' with gate counts and the number of successful rewrites.
optimiseWithStats
  :: forall a b
   . (KnownWires a, KnownWires b)
  => Netlist a b -> Either CircuitGraphError (Netlist a b, OptimisationStats)
optimiseWithStats n = do
  _ <- either (Left . InvalidCircuit) Right (prepare n)
  let original = toHypergraph n
      !before = gateCount original
      reduced = R.normalise R.unlimitedRewrites compiledRules original
      steps = fromIntegral (R.normalisationRewrites reduced)
  result <- fromHypergraph @a @b (R.normalisedGraph reduced)
  pure (result, OptimisationStats before (gateCount (toHypergraph result)) steps)

gateCount :: (a :: HG.OPENHG () Gate) ~> b -> Int
gateCount g = let (_, _, _, boxes) = HG.hypergraphParts g in length boxes

compiledRules :: R.CompiledRules Int () Gate
compiledRules = builtIn (R.compileRules (zip [0 ..] rules))

-- List order supplies the conflict priorities.
rules :: [R.Rule () Gate]
rules =
  [ notGate . notGate ==> x
  , notGate . constant False ==> constant True
  , notGate . constant True ==> constant False
  , andGate . (x &&& false) ==> false
  , andGate . (x &&& true) ==> x
  , andGate . (false &&& x) ==> false
  , andGate . (true &&& x) ==> x
  , andGate . (x &&& x) ==> x
  , andGate . (notGate &&& x) ==> false
  , andGate . (x &&& notGate) ==> false
  , orGate . (x &&& false) ==> x
  , orGate . (x &&& true) ==> true
  , orGate . (false &&& x) ==> x
  , orGate . (true &&& x) ==> true
  , orGate . (x &&& x) ==> x
  , orGate . (notGate &&& x) ==> true
  , orGate . (x &&& notGate) ==> true
  , xorGate . (x &&& false) ==> x
  , xorGate . (x &&& true) ==> notGate
  , xorGate . (false &&& x) ==> x
  , xorGate . (true &&& x) ==> notGate
  , xorGate . (x &&& x) ==> false
  , xorGate . (notGate &&& x) ==> true
  , xorGate . (x &&& notGate) ==> true
  , choose s v v ==> v
  , choose x x x ==> x
  , choose s s v ==> orGate
  , choose s v s ==> andGate
  , choose false s v ==> v
  , choose true s v ==> s
  , choose x false false ==> false
  , choose x false true ==> notGate
  , choose x true false ==> x
  , choose x true true ==> true
  , choose s true v ==> orGate
  , choose s v false ==> andGate
  ]
  where
    s, v :: Circuit (Bit ** Bit) Bit
    s = Copy.fst
    v = Copy.snd

    x :: Circuit Bit Bit
    x = id

    false, true :: (KnownWires a) => Circuit a Bit
    false = constant False . discard
    true = constant True . discard

    choose :: Circuit a Bit -> Circuit a Bit -> Circuit a Bit -> Circuit a Bit
    choose c a b = mux . ((c &&& a) &&& b)

infix 1 ==>

-- Local equations preserve all signals except the gate being replaced. Constants
-- and inverters on the left remain available to other consumers.
(==>) :: Circuit a Bit -> Circuit a Bit -> R.Rule () Gate
lhs ==> rhs = HG.reifySorts @() nodeSorts \ @as -> builtIn do
  l <- HG.openHypergraph @Gate @as @'[] nodeSorts boundary [] lhsBoxes
  r <- HG.openHypergraph @Gate @as @'[] rightSorts (map renumber images) [] (map (fmap renumber) replacement)
  R.rule l r
  where
    (nodeSorts, lhsInputs, lhsOutputs, lhsBoxes) = HG.hypergraphParts (toHypergraph (netlist lhs))
    (_, rhsInputs, rhsOutputs, rhsBoxes) = HG.hypergraphParts (toHypergraph (netlist rhs))
    result = singleOutput lhsOutputs
    boundary = [0 .. length nodeSorts - 1]
    witnesses = [b | b <- lhsBoxes, HG.outputs b /= [result]]
    -- Reuse matching left-side witnesses on the right, e.g. AND False x returns
    -- the existing False signal. Separate literal occurrences on the left remain
    -- separate nodes, so equal-valued constants need not already share a wire.
    (_, mapping, added) = foldl' add (length nodeSorts, IM.fromList (zip rhsInputs lhsInputs), []) rhsBoxes
    add (next, image, boxes) (HG.Box gate ins [out]) =
      let inputs = map (image IM.!) ins
      in case find (\b -> HG.label b == gate && HG.inputs b == inputs) witnesses of
           Just b -> (next, IM.insert out (singleOutput (HG.outputs b)) image, boxes)
           Nothing -> (next + 1, IM.insert out next image, HG.Box gate inputs [next] : boxes)
    add _ _ = error "CircuitRewrite: expected a single-output gate"
    replacement = witnesses ++ reverse added
    output = mapping IM.! singleOutput rhsOutputs
    images = [if n == result then output else n | n <- boundary]
    rightNodes = nubOrd (images ++ concat [ins ++ outs | HG.Box _ ins outs <- replacement])
    indices = IM.fromList (zip rightNodes [0 ..])
    renumber = (indices IM.!)
    rightSorts = concat (replicate (length rightNodes) (HG.sortList @() @'[ '()]))

singleOutput :: [Int] -> Int
singleOutput [n] = n
singleOutput _ = error "CircuitRewrite: expected a single bit output"

builtIn :: Either String a -> a
builtIn = either (error . ("CircuitRewrite: invalid built-in rule: " ++)) id

-- The two middle redundancies are surrounded by an AND gate and a register.
redundant :: Bit ** Bit ~> Bit
redundant =
  register True
    . notGate
    . notGate
    . andGate
    . (constant True ** andGate)
    . leftUnitorInv

doubleNotRule :: Either String (R.Rule () Gate)
doubleNotRule = R.rule (toHypergraph (netlist (notGate . notGate))) (toHypergraph (netlist (obj @Bit)))

-- Repeated rewrites, with validation before and after optimisation.
optimisedNetlist :: Either CircuitGraphError (Netlist (Bit ** Bit) Bit)
optimisedNetlist = optimise (netlist redundant)

runNetlist
  :: (KnownWires a, KnownWires b)
  => Netlist a b -> [Sample a] -> Either CircuitError [Sample b]
runNetlist n xs = do
  prepared <- prepare n
  pure (runSimulator (F.fmap @Value prepared) xs)

roundTrip
  :: forall a b
   . (KnownWires a, KnownWires b, Eq (Sample b), Show (Sample b))
  => Circuit a b -> [Sample a] -> Property ()
roundTrip c xs = case fromHypergraph @a @b (toHypergraph (netlist c)) of
  Left err -> testFailed (show err)
  Right n -> expect "round-trip simulation" (simulate c xs) (runNetlist n xs)

boxesOf :: (a :: HG.OPENHG () Gate) ~> b -> [HG.Box Gate Int]
boxesOf h = let (_, _, _, bs) = HG.hypergraphParts h in bs

graph
  :: (HG.SortList as, HG.SortList bs)
  => Int
  -> [Int]
  -> [Int]
  -> [HG.Box Gate Int]
  -> (HG.Wires as :: HG.OPENHG () Gate) ~> HG.Wires bs
graph n = HG.unsafeOpenHypergraph (concat (replicate n (HG.sortList @() @'[ '()])))

expectImportError
  :: forall a b
   . (KnownWires a, KnownWires b)
  => CircuitGraph a b -> CircuitGraphError -> Property ()
expectImportError g expected = case fromHypergraph @a @b g of
  Left err -> expect "import error" expected err
  Right _ -> testFailed "accepted an invalid circuit graph"

checkOptimisation
  :: (KnownWires a, KnownWires b, Eq (Sample b), Show (Sample b))
  => Circuit a b -> [Sample a] -> OptimisationStats -> Property ()
checkOptimisation c xs expected = case optimiseWithStats (netlist c) of
  Left err -> testFailed (show err)
  Right (n, stats) -> do
    expect "rewrite statistics" expected stats
    expect "simulation equivalence" (simulate c xs) (runNetlist n xs)
    case optimiseWithStats n of
      Left err -> testFailed (show err)
      Right (again, stable) -> do
        expect "fixed-point statistics" (OptimisationStats (gatesAfter stats) (gatesAfter stats) 0) stable
        check "fixed-point graph" (HG.isomorphic (toHypergraph n) (toHypergraph again))

test :: TestTree
test =
  testGroup
    "Circuit rewriting"
    [ testProperty "generated stateful circuits survive a round trip" $ do
        c <- genNamed @(Circuit (Bit ** Bit) (Bit ** Bit)) "circuit"
        xs <- genNamed @[(Bool, Bool)] "inputs"
        roundTrip c xs
    , testProperty "the counter preserves grouped outputs and feedback" $ do
        xs <- genNamed @[(Bool, Bool)] "enable/reset"
        roundTrip counter xs
    , testProperty "fan-out and unused input boundaries survive a round trip" $ do
        roundTrip (comult @Bit) [False, True]
        roundTrip (counit @Bit) [False, True]
        roundTrip (obj @Empty) [(), ()]
        roundTrip (constant True) [(), ()]
    , testProperty "register initialization and mux port order survive a round trip" $ do
        let bits = [False, True]
            pairs = [(a, b) | a <- bits, b <- bits]
        roundTrip notGate bits
        roundTrip andGate pairs
        roundTrip orGate pairs
        roundTrip xorGate pairs
        roundTrip mux [((s, a), b) | s <- bits, a <- bits, b <- bits]
        roundTrip (register False . register True) [True, False, False, True]
    , testProperty "two interior rewrites reduce six gates to two" $ do
        xs <- genNamed @[(Bool, Bool)] "clock inputs"
        case optimisedNetlist of
          Left err -> testFailed (show err)
          Right n -> do
            expect "original gate count" 6 (length (boxesOf (toHypergraph (netlist redundant))))
            expect "optimised gate count" 2 (length (boxesOf (toHypergraph n)))
            expect "unchanged outputs and initial register value" (simulate redundant xs) (runNetlist n xs)
            case toVerilog "optimised" n of
              Left err -> testFailed (show err)
              Right source -> do
                check "NOT gates remain" (not ("~" `isInfixOf` source))
                check "AND gate missing" (" & " `isInfixOf` source)
                check "register missing" ("always @(posedge clk)" `isInfixOf` source)
                check "initial value changed" ("1'b1" `isInfixOf` source)
    , testProperty "repeated rules simplify chains and parallel branches to a fixed point" $ do
        n <- Falsify.gen (Gen.elem (1 :| [2 .. 8]))
        xs <- genNamed @[Bool] "inputs"
        mapM_
          (\(c, before, steps) -> checkOptimisation c xs (OptimisationStats before 0 steps))
          [ (Workloads.chain n, 4 * n, 2 * n)
          , (Workloads.parallelBranches n, 5 * n - 1, 3 * n - 1)
          ]
    , testProperty "shared complemented signals simplify to false" $ do
        n <- Falsify.gen (Gen.elem (1 :| [2 .. 8]))
        xs <- genNamed @[Bool] "inputs"
        checkOptimisation (Workloads.sharedSignals n) xs (OptimisationStats (4 * n - 1) 1 (3 * n - 1))
    , testProperty "one snapshot batches independent parallel cancellations" $ do
        n <- Falsify.gen (Gen.elem (1 :| [2 .. 8]))
        xs <- genNamed @[Bool] "inputs"
        let c = Workloads.parallelBranches n
        case doubleNotRule of
          Left err -> testFailed err
          Right r -> do
            let (count, reduced) = R.rewriteBatch r (toHypergraph (netlist c))
            expect "all leaf cancellations in one batch" n count
            case fromHypergraph @Bit @Bit reduced of
              Left err -> testFailed (show err)
              Right result -> do
                expect "same behaviour" (simulate c xs) (runNetlist result xs)
                case optimiseWithStats result of
                  Left err -> testFailed (show err)
                  Right (_, stats) -> expect "AND identities and repeated inputs remain" (2 * n - 1) (rewriteSteps stats)
    , testProperty "later batches find matches enabled by another rule" $ do
        let c = notGate . andGate . (constant True ** notGate) . leftUnitorInv
        checkOptimisation c [False, True, False] (OptimisationStats 4 0 2)
    , testProperty "XOR of one signal with itself becomes a false constant" $ do
        let c = xorGate . comult @Bit
        checkOptimisation c [False, True] (OptimisationStats 1 1 1)
        case optimise (netlist c) of
          Left err -> testFailed (show err)
          Right n -> expect "constant replaces XOR" [ConstantGate False] [l | HG.Box l _ _ <- boxesOf (toHypergraph n)]
    , testProperty "XOR cancellation preserves surrounding state and prunes its unused producer" $ do
        let c = register True . notGate . xorGate . comult @Bit . notGate
        xs <- genNamed @[Bool] "inputs"
        checkOptimisation c xs (OptimisationStats 4 2 2)
    , testProperty "XOR cancellation retains shared producers and output fan-out" $ do
        let c :: Bit ~> Bit ** (Bit ** Bit)
            c = toSMC @(F Bit) @(F (Bit ** (Bit ** Bit))) \x -> SMC.do
              y <- notGate -< x
              z <- xorGate -< (y, y)
              returnA -< (y, (z, z))
        xs <- genNamed @[Bool] "inputs"
        checkOptimisation c xs (OptimisationStats 2 2 1)
    , testProperty "XOR cancellations sharing an input are batched" $ do
        let c = ((xorGate . comult @Bit) ** (xorGate . comult @Bit)) . comult @Bit
            lhs = toHypergraph (netlist (xorGate . comult @Bit))
            rhs = toHypergraph (netlist (constant False . counit @Bit))
        case R.rule lhs rhs of
          Left err -> testFailed err
          Right r -> do
            let (count, reduced) = R.rewriteBatch r (toHypergraph (netlist c))
            expect "both XORs in one batch" 2 count
            expect "two constants" [ConstantGate False, ConstantGate False] [l | HG.Box l _ _ <- boxesOf reduced]
        checkOptimisation c [False, True] (OptimisationStats 2 2 2)
    , testProperty "a compiled batch applies different circuit rules together" $ do
        let cancelXor = R.rule (toHypergraph (netlist (xorGate . comult @Bit))) (toHypergraph (netlist (constant False . counit @Bit)))
            c = ((notGate . notGate) ** (xorGate . comult @Bit)) . comult @Bit
            expected = (obj @Bit ** constant False) . rightUnitorInv
        case (doubleNotRule, cancelXor) of
          (Right a, Right b) -> case R.compileRules [(1 :: Int, b), (0, a)] of
            Left err -> testFailed err
            Right compiled -> do
              let (count, result) = R.rewriteBatchCompiled compiled (toHypergraph (netlist c))
              expect "both rule kinds in one batch" 2 count
              check "shared input and constant output" (HG.isomorphic (toHypergraph (netlist expected)) result)
          _ -> testFailed "invalid circuit rules"
        checkOptimisation c [False, True] (OptimisationStats 3 1 2)
    , testProperty "double negation can expose equal XOR inputs" $ do
        let c = xorGate . ((notGate . notGate) ** obj @Bit) . comult @Bit
        checkOptimisation c [False, True] (OptimisationStats 3 1 2)
    , testProperty "XOR of distinct signals is unchanged" $
        checkOptimisation xorGate [(a, b) | a <- [False, True], b <- [False, True]] (OptimisationStats 1 1 0)
    , booleanRules
    , testProperty "shared constants remain available to other consumers" $ do
        let c :: Bit ~> Bit ** (Bit ** Bit)
            c = toSMC @(F Bit) @(F (Bit ** (Bit ** Bit))) \x -> SMC.do
              t <- constant True -< ()
              a <- andGate -< (t, x)
              b <- xorGate -< (t, x)
              returnA -< (t, (a, b))
        checkOptimisation c [False, True] (OptimisationStats 3 2 2)
    , testProperty "constant folding preserves a shared NOT input" $ do
        let c :: Empty ~> Bit ** Bit
            c = toSMC @I @(F (Bit ** Bit)) \() -> SMC.do
              f <- constant False -< ()
              t <- notGate -< f
              returnA -< (f, t)
        checkOptimisation c [(), ()] (OptimisationStats 2 2 1)
    , testProperty "equal-valued mux branches can be separate shared constants" $
        mapM_
          ( \value -> do
              let c :: Bit ~> Bit ** (Bit ** Bit)
                  c = toSMC @(F Bit) @(F (Bit ** (Bit ** Bit))) \s -> SMC.do
                    a <- constant value -< ()
                    b <- constant value -< ()
                    y <- mux -< ((s, a), b)
                    returnA -< (a, (b, y))
              checkOptimisation c [False, True] (OptimisationStats 3 2 1)
          )
          [False, True]
    , testProperty "complement elimination preserves a shared inverter" $ do
        let c :: Bit ~> Bit ** Bit
            c = toSMC @(F Bit) @(F (Bit ** Bit)) \x -> SMC.do
              y <- notGate -< x
              z <- andGate -< (x, y)
              returnA -< (y, z)
        checkOptimisation c [False, True] (OptimisationStats 2 2 1)
    , testProperty "registers retain their initial value with constant inputs" $
        checkOptimisation (register True . constant False) [(), (), ()] (OptimisationStats 2 2 0)
    , testProperty "optimisation preserves generated stateful circuits" $ do
        c <- genNamed @(Circuit (Bit ** Bit) (Bit ** Bit)) "circuit"
        xs <- genNamed @[(Bool, Bool)] "inputs"
        case optimiseWithStats (netlist c) of
          Left err -> testFailed (show err)
          Right (n, stats) -> do
            expect "unchanged behaviour" (simulate c xs) (runNetlist n xs)
            check "gate count does not increase" (gatesAfter stats <= gatesBefore stats)
            let ports net = sum [length ins | HG.Box _ ins _ <- boxesOf (toHypergraph net)]
            check "gate input ports decrease with each rewrite" (rewriteSteps stats <= ports (netlist c) - ports n)
            case optimiseWithStats n of
              Left err -> testFailed (show err)
              Right (_, stable) -> expect "local fixed point" 0 (rewriteSteps stable)
    , testProperty "optimisation preserves the counter" $ do
        xs <- genNamed @[(Bool, Bool)] "enable/reset"
        case optimise (netlist counter) of
          Left err -> testFailed (show err)
          Right n -> expect "counter outputs" (simulate counter xs) (runNetlist n xs)
    , testProperty "invalid input is rejected before simplification" $ do
        let loop :: Empty ~> Bit
            loop = toSMC @I @(F Bit) \() -> SMC.do
              rec x <- notGate -< x
              returnA -< x
        case optimise (netlist loop) of
          Left (InvalidCircuit (CombinationalCycle _)) -> pure ()
          Left err -> testFailed (show err)
          Right _ -> testFailed "accepted invalid input"
    , testProperty "double negation simplifies while retaining a shared intermediate inverter" $ do
        let shared :: Bit ~> Bit ** Bit
            shared = toSMC @(F Bit) @(F (Bit ** Bit)) \x -> SMC.do
              y <- notGate -< x
              z <- notGate -< y
              returnA -< (y, z)
        checkOptimisation shared [False, True, False] (OptimisationStats 2 1 1)
        case doubleNotRule of
          Left err -> testFailed err
          Right r -> expect "a deleting rule still fails the dangling check" 0 (length (R.rewrites r (toHypergraph (netlist shared))))
    , testProperty "every larger-graph occurrence is offered separately" $ do
        let c = register False . notGate . notGate . notGate . notGate
        case doubleNotRule of
          Left err -> testFailed err
          Right r -> do
            let results = R.rewrites r (toHypergraph (netlist c))
            expect "three overlapping occurrences" 3 (length results)
            mapM_
              ( \g -> case fromHypergraph @Bit @Bit g of
                  Left err -> testFailed (show err)
                  Right n -> expect "each rewrite preserves behaviour" (simulate c [True, False, True]) (runNetlist n [True, False, True])
              )
              results
    , testProperty "gate arities are validated" $
        expectImportError @Bit @Bit
          (graph 2 [0] [1] [HG.Box AndGate [0] [1]])
          (InvalidGateArity AndGate 1 1)
    , testProperty "each gate must have one output" $
        expectImportError @Bit @Bit
          (graph 2 [0] [1] [HG.Box NotGate [0] [0, 1]])
          (InvalidGateArity NotGate 1 2)
    , testProperty "a gate cannot drive an input signal" $
        expectImportError @Bit @Bit
          (graph 1 [0] [0] [HG.Box (ConstantGate True) [] [0]])
          (MultipleDrivers [0])
    , testProperty "two gate outputs cannot share a signal" $
        expectImportError @Empty @Bit
          (graph 1 [] [0] [HG.Box (ConstantGate True) [] [0], HG.Box (ConstantGate False) [] [0]])
          (MultipleDrivers [0])
    , testProperty "independent input positions cannot be identified" $
        expectImportError @(Bit ** Bit) @Bit (graph 1 [0, 0] [0] []) (MultipleDrivers [0])
    , testProperty "undriven output signals are rejected" $
        expectImportError @Bit @Bit (graph 2 [0] [1] []) (UndrivenSignals [1])
    , testProperty "observable combinational cycles are rejected" $
        case fromHypergraph @Empty @Bit (graph 1 [] [0] [HG.Box NotGate [0] [0]]) of
          Left (InvalidCircuit (CombinationalCycle ns)) -> check "missing cycle" (not (null ns))
          Left err -> testFailed (show err)
          Right _ -> testFailed "accepted inverter feedback"
    , testProperty "an exported alias-only loop remains invalid" $ do
        let loop :: Empty ~> Bit
            loop = toSMC @I @(F Bit) \() -> SMC.do
              rec x <- id @Circuit @Bit -< x
              returnA -< x
        case fromHypergraph @Empty @Bit (toHypergraph (netlist loop)) of
          Left (UndrivenSignals ns) -> check "missing undriven node" (not (null ns))
          Left err -> testFailed (show err)
          Right _ -> testFailed "accepted alias-only feedback"
    , testProperty "unused combinational cycles are pruned before preparation" $
        case fromHypergraph @Bit @Bit (graph 2 [0] [0] [HG.Box NotGate [1] [1]]) of
          Left err -> testFailed (show err)
          Right n -> do
            expect "unused gate removed" 0 (length (boxesOf (toHypergraph n)))
            expect "identity" (Right [False, True]) (runNetlist n [False, True])
    ]

-- Each fixture checks every input assignment, the expected remaining gate kinds,
-- that a rewrite actually happened, and that a second optimisation is stable.
booleanCase :: (KnownWires a) => String -> Circuit a Bit -> [Sample a] -> [Gate] -> TestTree
booleanCase name c xs remaining = testProperty name $ case optimiseWithStats (netlist c) of
  Left err -> testFailed (show err)
  Right (n, stats) -> do
    expect "truth table" (simulate c xs) (runNetlist n xs)
    expect "remaining gates" (sort remaining) (sort [l | HG.Box l _ _ <- boxesOf (toHypergraph n)])
    check "rule applied" (rewriteSteps stats > 0)
    case optimiseWithStats n of
      Left err -> testFailed (show err)
      Right (_, stable) -> expect "local fixed point" 0 (rewriteSteps stable)

booleanRules :: TestTree
booleanRules =
  testGroup "Boolean rules" $
    [booleanCase "double negation" (notGate . notGate) bits []]
      ++ [ booleanCase ("NOT " ++ show b) (notGate . constant b) [()] [ConstantGate (not b)]
         | b <- bits
         ]
      ++ concat
        [ [ booleanCase
              (name ++ " constant " ++ show (side, b))
              (gate . operand side b)
              bits
              (unary (operation b False) (operation b True))
          | side <- bits
          , b <- bits
          ]
            ++ [booleanCase (name ++ " repeated input") (gate . comult @Bit) bits [ConstantGate False | name == "XOR"]]
            ++ [ booleanCase (name ++ " complement " ++ show side) (gate . complementary side) bits [ConstantGate (operation False True)]
               | side <- bits
               ]
            ++ [ booleanCase
                   (name ++ " constants " ++ show (a, b))
                   (gate . (constant a ** constant b) . leftUnitorInv)
                   [()]
                   [ConstantGate (operation a b)]
               | a <- bits
               , b <- bits
               ]
        | (name, gate, operation) <- [("AND", andGate, (&&)), ("OR", orGate, (||)), ("XOR", xorGate, (/=))]
        ]
      ++ [ booleanCase ("mux selector " ++ show s) (mux . selector s) pairs []
         | s <- bits
         ]
      ++ [booleanCase "mux equal branches" equalBranches pairs []]
      ++ [booleanCase "mux all inputs equal" (mux . (comult @Bit ** obj @Bit) . comult @Bit) bits []]
      ++ [ booleanCase "mux selector is true branch" selectorTrue pairs [OrGate]
         , booleanCase "mux selector is false branch" selectorFalse pairs [AndGate]
         ]
      ++ [ booleanCase ("mux constant branches " ++ show (a, b)) (mux . branches a b) bits (unary b a)
         | a <- bits
         , b <- bits
         ]
      ++ [ booleanCase
             ("constant mux " ++ show (s, a, b))
             (mux . branches a b . constant s)
             [()]
             [ConstantGate (if s then a else b)]
         | s <- bits
         , a <- bits
         , b <- bits
         ]
      ++ [ booleanCase "mux True branch" trueBranch pairs [OrGate]
         , booleanCase "mux False branch" falseBranch pairs [AndGate]
         ]
  where
    bits = [False, True]
    pairs = [(a, b) | a <- bits, b <- bits]
    unary False True = []
    unary True False = [NotGate]
    unary b _ = [ConstantGate b]
    operand side b = if side then (constant b ** obj @Bit) . leftUnitorInv else (obj @Bit ** constant b) . rightUnitorInv
    complementary side = (if side then obj @Bit ** notGate else notGate ** obj @Bit) . comult @Bit
    selector s = ((constant s ** obj @Bit) ** obj @Bit) . (leftUnitorInv ** obj @Bit)
    branches a b = ((obj @Bit ** constant a) ** constant b) . rightUnitorInv . rightUnitorInv
    equalBranches = mux . associatorInv . (obj @Bit ** comult @Bit)
    selectorTrue = toSMC @(F (Bit ** Bit)) @(F Bit) \(s, b) -> SMC.do
      y <- mux -< ((s, s), b)
      returnA -< y
    selectorFalse = toSMC @(F (Bit ** Bit)) @(F Bit) \(s, a) -> SMC.do
      y <- mux -< ((s, a), s)
      returnA -< y
    trueBranch = toSMC @(F (Bit ** Bit)) @(F Bit) \(s, b) -> SMC.do
      t <- constant True -< ()
      y <- mux -< ((s, t), b)
      returnA -< y
    falseBranch = toSMC @(F (Bit ** Bit)) @(F Bit) \(s, a) -> SMC.do
      f <- constant False -< ()
      y <- mux -< ((s, a), f)
      returnA -< y
