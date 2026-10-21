{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | A four-bit counter with enable and synchronous reset, built from Boolean gates and registers.
module Examples.Circuit
  ( test
  , Word4
  , increment
  , mux4
  , register4
  , counter
  , fromInt
  , toInt
  , demoInputs
  , demoOutputs
  , counterPicture
  , expandedCounterPicture
  , simplifiedCounterPicture
  , waveform
  , counterTestbench
  ) where

import Data.Bits (testBit)
import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.Circuit
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.Simulator (runSimulator)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal)
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Functor qualified as F
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))
import Proarrow.Testing (check, expect, genNamed)
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)
import Proarrow.Tools.SMC (SYN (..), returnA, toSMC, unit, (-<))
import Proarrow.Tools.SMC qualified as SMC
import Props.Hask ()

-- In GHCi, from the repository root:
--
-- cabal repl test:test
-- :module *Examples.Circuit
-- demoOutputs
-- writeFile "/tmp/counter.svg" counterPicture
-- writeFile "/tmp/counter-expanded.svg" expandedCounterPicture
-- either fail (writeFile "/tmp/counter-simplified.svg") simplifiedCounterPicture
-- either (fail . show) (writeFile "/tmp/waveform.svg") waveform
-- writeFile "/tmp/counter.dot" (toDot (netlist counter))
-- :! dot -Tsvg /tmp/counter.dot -o /tmp/gates.svg
-- either (fail . show) (writeFile "/tmp/counter.v") (toVerilog "counter" (netlist counter))
-- either (fail . show) (writeFile "/tmp/counter_tb.v") counterTestbench
-- :! iverilog -g2012 -s tb -o /tmp/counter_sim /tmp/counter.v /tmp/counter_tb.v
-- :! vvp /tmp/counter_sim
--
-- The compact diagram uses one wire per word, labelled b₁ for control bits and b₄ for four-bit words.
-- Expanded ports are ordered enable, reset on the input and least-significant bit first on the output.

type Word4 :: Wires
type Word4 = Bit ** Bit ** Bit ** Bit

type Word4S :: k -> SYN k
type Word4S b = F b :** F b :** F b :** F b

-- | Ripple carries through the lower bits; overflow is discarded.
increment :: Word4 ~> Word4
increment = incrementWith @Bit (constant True) xorGate andGate

incrementWith
  :: forall {k} (b :: k)
   . (CocommutativeComonoid b)
  => (Unit ~> b) -> (b ** b ~> b) -> (b ** b ~> b) -> b ** b ** b ** b ~> b ** b ** b ** b
incrementWith high xorG andG = toSMC @(Word4S b) @(Word4S b) \(a, b, c, d) -> SMC.do
  (a', carry1) <- SMC.recast @_ @(F b :** F b) (halfAdder -< (a, high -< unit))
  (b', carry2) <- SMC.recast @_ @(F b :** F b) (halfAdder -< (b, carry1))
  (c', carry3) <- SMC.recast @_ @(F b :** F b) (halfAdder -< (c, carry2))
  a' SMC.** b' SMC.** c' SMC.** (xorG -< (d, carry3))
  where
    halfAdder :: b ** b ~> b ** b
    halfAdder = toSMC @(F b :** F b) @(F b :** F b) \(a, b) ->
      (xorG -< (a, b)) SMC.** (andG -< (a, b))

mux4 :: Bit ** Word4 ** Word4 ~> Word4
mux4 = mux4With @Bit mux

mux4With
  :: forall {k} (b :: k)
   . (CocommutativeComonoid b)
  => (b ** b ** b ~> b) -> b ** (b ** b ** b ** b) ** (b ** b ** b ** b) ~> b ** b ** b ** b
mux4With select = toSMC @(F b :** Word4S b :** Word4S b) @(Word4S b) \(s, (a, b, c, d), (w, x, y, z)) ->
  (select -< (s, a, w)) SMC.** (select -< (s, b, x)) SMC.** (select -< (s, c, y)) SMC.** (select -< (s, d, z))

register4 :: Int -> Word4 ~> Word4
register4 n = register a ** register b ** register c ** register d
  where
    (((a, b), c), d) = fromInt n

zero4 :: Empty ~> Word4
zero4 = zero4With @Bit (constant False)

zero4With :: forall {k} (b :: k). (CocommutativeComonoid b) => (Unit ~> b) -> Unit ~> b ** b ** b ** b
zero4With low = toSMC @I @(Word4S b) \() -> SMC.do
  z <- low -< unit
  z SMC.** z SMC.** z SMC.** z

-- | Enable holds or increments the count. Synchronous reset has priority over enable.
-- The initial output is zero; controls determine the output after the next clock edge.
counter :: Bit ** Bit ~> Word4
counter = counterWith @Bit @Word4 zero4 mux4 increment (register4 0)

counterWith
  :: forall {k} (b :: k) w
   . (TracedMonoidal k, CocommutativeComonoid w, Ob b)
  => (Unit ~> w) -> (b ** w ** w ~> w) -> (w ~> w) -> (w ~> w) -> b ** b ~> w
counterWith zero select inc delay = toSMC @(F b :** F b) @(F w) \(enable, reset) -> SMC.do
  rec count <- delay -< (select -< (reset, zero -< unit, select -< (enable, inc -< count, count)))
  returnA -< count

-- | The same counter with word-sized components, rather than their expanded bit-level gates.
counterPicture :: String
counterPicture = render (counterWith @Control @Bus (node "0") (node "mux4") (node "increment") (node "D4 (0)"))

-- | The same counter expanded into individual Boolean gates and one-bit registers.
expandedCounterPicture :: String
expandedCounterPicture =
  render $
    counterWith @Control @(Control ** Control ** Control ** Control)
      (zero4With @Control (node "0"))
      (mux4With @Control (node "MUX"))
      (incrementWith @Control (node "1") (node "XOR") (node "AND"))
      (delay ** delay ** delay ** delay)
  where
    delay :: Control ~> Control
    delay = node "D (0)"

-- | The expanded counter read back in parallel layers using traced copy/discard wiring.
simplifiedCounterPicture :: Either String String
simplifiedCounterPicture = do
  Str diagram <- HG.simplify (HG.layered (HG.tracedWith HG.copyDiscard)) expandedCounterGraph
  pure (render diagram)

type GraphBit :: HG.SIMPLIFY SVG
type GraphBit = HG.Wires '[Control]

expandedCounterGraph :: GraphBit ** GraphBit ~> GraphBit ** GraphBit ** GraphBit ** GraphBit
expandedCounterGraph =
  counterWith @GraphBit @(GraphBit ** GraphBit ** GraphBit ** GraphBit)
    (zero4With @GraphBit (HG.prim @'[] @'[Control] (Str (node "0"))))
    (mux4With @GraphBit (HG.prim @'[Control, Control, Control] @'[Control] (Str (node "MUX"))))
    ( incrementWith @GraphBit
        (HG.prim @'[] @'[Control] (Str (node "1")))
        (HG.prim @'[Control, Control] @'[Control] (Str (node "XOR")))
        (HG.prim @'[Control, Control] @'[Control] (Str (node "AND")))
    )
    (delay ** delay ** delay ** delay)
  where
    delay :: GraphBit ~> GraphBit
    delay = HG.prim @'[Control] @'[Control] (Str (node "D (0)"))

type Control :: SVG
type Control = S '[Wire "b₁"]
type Bus :: SVG
type Bus = S '[Wire "b₄"]

fromInt :: Int -> Sample Word4
fromInt n = (((testBit n 0, testBit n 1), testBit n 2), testBit n 3)

toInt :: Sample Word4 -> Int
toInt (((a, b), c), d) = sum [weight | (bit, weight) <- zip [a, b, c, d] [1, 2, 4, 8], bit]

demoInputs :: [(Bool, Bool)]
demoInputs = replicate 18 (True, False) ++ replicate 3 (False, False) ++ [(True, True)] ++ replicate 5 (True, False)

demoOutputs :: Either CircuitError [Int]
demoOutputs = map toInt <$> simulate counter demoInputs

-- | A self-checking Verilog testbench using the simulator's expected counter outputs.
counterTestbench :: Either CircuitError String
counterTestbench = draw <$> demoOutputs
  where
    draw ns =
      unlines $
        [ "module tb;"
        , "  reg clk = 0;"
        , "  reg enable, reset;"
        , "  wire [3:0] count;"
        , "  counter dut(.clk(clk), .in0(enable), .in1(reset),"
        , "    .out0(count[0]), .out1(count[1]), .out2(count[2]), .out3(count[3]));"
        , "  initial begin"
        ]
          ++ concat [cycleLines i controls n | (i, controls, n) <- zip3 [0 :: Int ..] demoInputs ns]
          ++ [ "    $display(\"Counter matches simulator for " ++ show (length ns) ++ " cycles\");"
             , "    $finish;"
             , "  end"
             , "endmodule"
             ]
    cycleLines i (enable, reset) n =
      [ "    enable = " ++ bit enable ++ "; reset = " ++ bit reset ++ ";"
      , "    #1; if (count !== 4'd" ++ show n ++ ") $fatal(1, \"cycle " ++ show i ++ ": got %d\", count);"
      , "    #1 clk = 1; #1 clk = 0;"
      ]
    bit False = "1'b0"
    bit True = "1'b1"

-- | A waveform of the counter outputs before each clock edge and the controls for that cycle.
waveform :: Either CircuitError String
waveform = draw <$> demoOutputs
  where
    draw ns =
      unlines $
        [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\""
            ++ show width
            ++ "\" height=\"300\" viewBox=\"0 0 "
            ++ show width
            ++ " 300\">"
        , "<style>text{font:12px monospace;fill:#1f2328}path,line{fill:none;stroke:#0969da;stroke-width:2}.grid{stroke:#d0d7de;stroke-width:1}</style>"
        , "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>"
        , text 12 20 "Four-bit counter: values before each clock edge"
        ]
          ++ [ "<line class=\"grid\" x1=\"" ++ show (x i) ++ "\" y1=\"32\" x2=\"" ++ show (x i) ++ "\" y2=\"275\"/>"
             | i <- [0 .. length ns]
             ]
          ++ [text (x i + 8) 44 (show i) | i <- [0 .. length ns - 1]]
          ++ concat [row y name samples | (y, name, samples) <- rows ns]
          ++ [text 12 279 "count"]
          ++ [text (x i + 8) 279 (show n) | (i, n) <- zip [0 ..] ns]
          ++ ["</svg>"]
    width = 100 + 28 * length demoInputs
    x :: Int -> Int
    x i = 84 + 28 * i
    text a b s = "<text x=\"" ++ show (a :: Int) ++ "\" y=\"" ++ show (b :: Int) ++ "\">" ++ s ++ "</text>"
    rows ns =
      [(70, "enable", map fst demoInputs), (102, "reset", map snd demoInputs)]
        ++ [(134 + 32 * bit, "q" ++ show bit, map (`testBit` bit) ns) | bit <- [0 .. 3]]
    row y name samples = [text 12 (y + 5) name, "<path d=\"" ++ unwords (segments y samples) ++ "\"/>"]
    segments :: Int -> [Bool] -> [String]
    segments _ [] = []
    segments y (b : bs) = ("M " ++ show (x 0) ++ " " ++ show (level b)) : go 0 b bs
      where
        level v = if v then y - 8 else y + 8
        go i _ [] = ["H " ++ show (x (i + 1))]
        go i previous (v : vs) = ("H " ++ show (x (i + 1)) ++ if previous == v then "" else " V " ++ show (level v)) : go (i + 1) v vs

bits :: [Bool]
bits = [False, True]

badLoop :: Empty ~> Bit
badLoop = toSMC @I @(F Bit) \() -> SMC.do
  rec x <- notGate -< x
  returnA -< x

test :: TestTree
test =
  testGroup
    "Digital circuits"
    [ testProperty "Boolean gate truth tables" do
        let pairs = [(a, b) | a <- bits, b <- bits]
            triples = [((s, a), b) | s <- bits, a <- bits, b <- bits]
        expect "NOT" (Right (map not bits)) (simulate notGate bits)
        expect "AND" (Right (map (uncurry (&&)) pairs)) (simulate andGate pairs)
        expect "OR" (Right (map (uncurry (||)) pairs)) (simulate orGate pairs)
        expect "XOR" (Right (map (uncurry (/=)) pairs)) (simulate xorGate pairs)
        expect "MUX" (Right [if s then a else b | ((s, a), b) <- triples]) (simulate mux triples)
        expect "low" (Right [False, False]) (simulate (constant False) [(), ()])
        expect "high" (Right [True, True]) (simulate (constant True) [(), ()])
    , testProperty "wiring preserves grouped bundles, copies and discards" do
        let xs = [((a, b), c) | a <- bits, b <- bits, c <- bits]
            wire :: Bit ** Bit ** Bit ~> Bit ** Bit ** Bit
            wire = toSMC @(F Bit :** F Bit :** F Bit) @(F (Bit ** Bit ** Bit)) \(a, _b, c) -> returnA -< (c, a, c)
        expect "fan-out and unused input" (Right [((c, a), c) | ((a, _), c) <- xs]) (simulate wire xs)
        expect "associators" (Right xs) (simulate (associatorInv . associator @Wires @Bit @Bit @Bit) xs)
        expect "left unitors" (Right bits) (simulate (leftUnitor . leftUnitorInv @Wires @Bit) bits)
        expect "right unitors" (Right bits) (simulate (rightUnitor . rightUnitorInv @Wires @Bit) bits)
        expect
          "swap twice"
          (Right [(a, b) | a <- bits, b <- bits])
          (simulate (swap . swap @Wires @Bit @Bit) [(a, b) | a <- bits, b <- bits])
        expect "trace yanking" (Right bits) (simulate (coact @Tensor @Circuit @Bit (swap @Wires @Bit @Bit)) bits)
        expect "copy then discard" (Right bits) (simulate (leftUnitor . (counit @Bit ** obj @Bit) . comult @Bit) bits)
    , testProperty "registers delay inputs and start at their declared values" do
        xs <- genNamed @[Bool] "inputs"
        expect "initial false" (Right (take (length xs) (False : xs))) (simulate (register False) xs)
        expect "initial true" (Right (take (length xs) (True : xs))) (simulate (register True) xs)
        expect
          "two cascaded registers"
          (Right (take (length xs) (False : True : xs)))
          (simulate (register False . register True) xs)
    , testProperty "parallel registers update simultaneously" do
        let exchange :: Empty ~> Bit ** Bit
            exchange = toSMC @I @(F (Bit ** Bit)) \() -> SMC.do
              rec (a, b) <- (register False ** register True) -< (b, a)
              returnA -< (a, b)
        expect "exchange" (Right (take 8 (cycle [(False, True), (True, False)]))) (simulate exchange (replicate 8 ()))
    , testProperty "increment wraps and bundle multiplexers select all four bits" do
        expect
          "all increments"
          (Right [fromInt ((n + 1) `mod` 16) | n <- [0 .. 15]])
          (simulate increment (map fromInt [0 .. 15]))
        let xs = [((s, fromInt a), fromInt b) | s <- bits, a <- [0 .. 15], b <- [0 .. 15]]
        expect "all word selections" (Right [if s then a else b | ((s, a), b) <- xs]) (simulate mux4 xs)
    , testProperty "counter follows an independent clocked specification" do
        controls <- genNamed @[(Bool, Bool)] "enable/reset"
        let model _ [] = []
            model n ((enable, reset) : xs) = n : model (if reset then 0 else if enable then (n + 1) `mod` 16 else n) xs
        expect "counter" (Right (model 0 controls)) (fmap (map toInt) (simulate counter controls))
        expect "demo wraps, holds and resets" (Right ([0 .. 15] ++ [0, 1, 2, 2, 2, 2, 0, 1, 2, 3, 4])) demoOutputs
    , testProperty "observable combinational cycles are rejected before any samples run" do
        check
          "inverter feedback accepted"
          (case simulate badLoop [] of Left (CombinationalCycle ns) -> not (null ns); _ -> False)
        let bare :: Empty ~> Bit
            bare = toSMC @I @(F Bit) \() -> SMC.do
              rec x <- id @Circuit @Bit -< x
              returnA -< x
        check "unconnected feedback accepted" (case simulate bare [] of Left (CombinationalCycle _) -> True; _ -> False)
    , testProperty "multiplexer validation checks both data inputs" do
        let selectedConstant :: Empty ~> Bit
            selectedConstant = toSMC @I @(F Bit) \() -> SMC.do
              x <- badLoop -< unit
              mux -< (constant True -< unit, constant False -< unit, x)
        check
          "cycle in unselected input accepted"
          (case simulate selectedConstant [] of Left (CombinationalCycle _) -> True; _ -> False)
    , testProperty "unobservable feedback is omitted from the netlist" do
        let dead = toSMC @I @I \() -> SMC.do
              _unused <- badLoop -< unit
              unit
        expect "discarded loop" (Right [(), ()]) (simulate dead [(), ()])
    , testProperty "preparing composition and tensor agrees with composing prepared circuits" do
        xs <- genNamed @[Bool] "clock inputs"
        case (prepare (netlist (register False)), prepare (netlist (register True))) of
          (Right f, Right g) -> do
            expect "composition" (simulate (register False . register True) xs) (Right (runSimulator (F.fmap @Value (f . g)) xs))
            expect
              "tensor"
              (simulate (register False ** register True) (zip xs xs))
              (Right (runSimulator (F.fmap @Value (f ** g)) (zip xs xs)))
          _ -> check "valid registers rejected" False
    , testProperty "netlist and waveform artifacts contain the circuit" do
        let n = netlist counter
        check "no counter diagram" ("<svg" `isInfixOf` counterPicture && "increment" `isInfixOf` counterPicture)
        check
          "no expanded counter diagram"
          ("<svg" `isInfixOf` expandedCounterPicture && "XOR" `isInfixOf` expandedCounterPicture)
        check "no registers in netlist" ("Register False" `isInfixOf` renderNetlist n)
        check "no register in diagram" ("D 0" `isInfixOf` toDot n)
        check "no waveform" (case waveform of Right svg -> "<svg" `isInfixOf` svg && "count" `isInfixOf` svg; _ -> False)
    , testProperty "Verilog preserves ports and register initialization" do
        case toVerilog "counter" (netlist counter) of
          Left err -> check (show err) False
          Right source -> do
            check "missing counter interface" ("module counter(input wire clk, input wire in0, input wire in1," `isInfixOf` source)
            check "missing most-significant output" ("output wire out3" `isInfixOf` source)
            check "missing register initialization" (" = 1'b0;" `isInfixOf` source && "initial w" `isInfixOf` source)
            check "missing rising-edge register" ("always @(posedge clk)" `isInfixOf` source && " <= w" `isInfixOf` source)
        check "combinational loop accepted" (case toVerilog "bad" (netlist badLoop) of Left _ -> True; _ -> False)
        expect
          "empty interface"
          (Right "module empty(input wire clk);\nendmodule\n")
          (toVerilog "empty" (netlist (id @Circuit @Empty)))
    ]
