{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Synchronous digital circuits. The tensor preserves the grouping of bit bundles; copying is
-- fan-out, and tracing connects wires without adding a delay. 'register' delays a bit by one
-- clock cycle. 'prepare' rejects observable combinational cycles before simulation.
--
-- >>> simulate notGate [False, True]
-- Right [True,False]
-- >>> simulate (register False) [True, False, True]
-- Right [False,True,False]
module Proarrow.Category.Instance.Circuit
  ( Wires (..)
  , KnownWires
  , Value
  , Sample
  , PREPARED (..)
  , Prepared
  , Circuit
  , constant
  , notGate
  , andGate
  , orGate
  , xorGate
  , mux
  , register
  , Netlist
  , netlist
  , renderNetlist
  , toDot
  , toVerilog
  , CircuitError (..)
  , Simulator
  , prepare
  , step
  , simulate
  ) where

import Control.Monad ((>=>))
import Data.Graph (SCC (..), stronglyConnComp)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Constraint, Type)
import Data.List qualified as List
import Prelude hiding (Functor, fmap, id, (**), (.))
import Prelude qualified as P

import Proarrow.Category.Instance.Simulator (SIMULATOR (..), Simulator (..), runSimulator, step)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (CocommutativeComonoid, Comonoid (..))
import Proarrow.Profunctor.Representable (Rep (..))

-- | A bit, no wires, or two bundles. Tensor grouping is retained in the type.
type data Wires = Bit | Empty | Pair Wires Wires

type Shape :: Wires -> Type
data Shape a where
  BitS :: Shape Bit
  EmptyS :: Shape Empty
  PairS :: Shape a -> Shape b -> Shape (Pair a b)

type KnownWires :: Wires -> Constraint
class (Is Sim (Value @ Ready a)) => KnownWires a where
  shape :: Shape a
instance KnownWires Bit where shape = BitS
instance KnownWires Empty where shape = EmptyS
instance (KnownWires a, KnownWires b) => KnownWires (Pair a b) where shape = PairS (shape @a) (shape @b)

-- | Objects of validated circuits, with the same wire shapes as 'Wires'.
type data PREPARED = Ready Wires

-- | Interpret validated circuits as state machines. Bits become 'Bool', the unit becomes @()@,
-- and a tensor becomes a pair, all in the 'SIMULATOR' category.
data family Value :: PREPARED +-> SIMULATOR

-- | The Haskell value for one clock cycle at a wire shape.
type Sample :: Wires -> Type
type Sample a = UN Sim (Value @ Ready a)

type Bundle :: Wires -> Type
data Bundle a where
  BBit :: Int -> Bundle Bit
  BEmpty :: Bundle Empty
  BPair :: Bundle a -> Bundle b -> Bundle (Pair a b)

ports :: Bundle a -> [Int]
ports bundle = go bundle []
  where
    go :: Bundle b -> [Int] -> [Int]
    go (BBit n) rest = n : rest
    go BEmpty rest = rest
    go (BPair a b) rest = go a (go b rest)

inputValues :: Bundle a -> Sample a -> [(Int, Bool)]
inputValues bundle value = go bundle value []
  where
    go :: Bundle b -> Sample b -> [(Int, Bool)] -> [(Int, Bool)]
    go (BBit n) bit rest = (n, bit) : rest
    go BEmpty () rest = rest
    go (BPair a b) (x, y) rest = go a x (go b y rest)

output :: Bundle a -> IM.IntMap Bool -> Sample a
output (BBit n) bs = bs IM.! n
output BEmpty _ = ()
output (BPair a b) bs = (output a bs, output b bs)

-- Each bit has one driver. Aliases connect the placeholders allocated by a trace.
data Driver
  = Input
  | Constant Bool
  | Not Int
  | And Int Int
  | Or Int Int
  | Xor Int Int
  | Mux Int Int Int
  | Register Bool Int
  | Alias Int
  deriving (Show)

inputs :: Driver -> [Int]
inputs Input = []
inputs (Constant _) = []
inputs (Not a) = [a]
inputs (And a b) = [a, b]
inputs (Or a b) = [a, b]
inputs (Xor a b) = [a, b]
inputs (Mux s a b) = [s, a, b]
inputs (Register _ a) = [a]
inputs (Alias a) = [a]

data BuildState = BuildState Int (IM.IntMap Driver)
newtype Build a = Build {runBuild :: BuildState -> (a, BuildState)}
instance P.Functor Build where
  fmap f (Build g) = Build \s -> let (x, s') = g s in (f x, s')
instance Applicative Build where
  pure x = Build (x,)
  f <*> x = do g <- f; g <$> x
instance Monad Build where
  Build f >>= k = Build \s -> let (x, s') = f s in runBuild (k x) s'

fresh :: Driver -> Build Int
fresh d = Build \(BuildState n ds) -> (n, BuildState (n + 1) (IM.insert n d ds))

freshBundle :: Driver -> Shape a -> Build (Bundle a)
freshBundle d BitS = BBit <$> fresh d
freshBundle _ EmptyS = pure BEmpty
freshBundle d (PairS a b) = BPair <$> freshBundle d a <*> freshBundle d b

connect :: Bundle a -> Bundle a -> Build ()
connect (BBit a) (BBit b) = Build \(BuildState n ds) -> ((), BuildState n (IM.insert a (Alias b) ds))
connect BEmpty BEmpty = pure ()
connect (BPair a b) (BPair c d) = connect a c >> connect b d

-- | A typed circuit builder. Constructors are hidden so every output bit has one driver.
type Circuit :: CAT Wires
data Circuit a b where
  Circuit :: (KnownWires a, KnownWires b) => (Bundle a -> Build (Bundle b)) -> Circuit a b

instance CategoryOf Wires where
  type (~>) = Circuit
  type Ob a = KnownWires a
instance Profunctor Circuit where
  dimap = dimapDefault
  r \\ Circuit{} = r
instance Promonad Circuit where
  id = Circuit pure
  Circuit f . Circuit g = Circuit (g >=> f)
instance MonoidalProfunctor Circuit where
  one = Circuit pure
  Circuit f ** Circuit g = Circuit \(BPair a b) -> BPair <$> f a <*> g b
instance Monoidal Wires where
  type Unit = Empty
  type a ** b = Pair a b
  withOb2 r = r
  leftUnitor = Circuit \(BPair BEmpty a) -> pure a
  leftUnitorInv = Circuit \a -> pure (BPair BEmpty a)
  rightUnitor = Circuit \(BPair a BEmpty) -> pure a
  rightUnitorInv = Circuit \a -> pure (BPair a BEmpty)
  associator = Circuit \(BPair (BPair a b) c) -> pure (BPair a (BPair b c))
  associatorInv = Circuit \(BPair a (BPair b c)) -> pure (BPair (BPair a b) c)
instance SymMonoidal Wires where
  swap = Circuit \(BPair a b) -> pure (BPair b a)
instance (KnownWires a) => Comonoid a where
  counit = Circuit \_ -> pure BEmpty
  comult = Circuit \a -> pure (BPair a a)
instance (KnownWires a) => CocommutativeComonoid a
instance CopyDiscard Wires
instance Costrong Tensor Circuit where
  coact @a (Circuit f) = Circuit \x -> do
    feedback <- freshBundle Input (shape @a)
    result <- f (BPair feedback x)
    case result of
      BPair feedback' y -> do
        connect feedback feedback'
        pure y

-- | A constant bit, independent of the clock.
constant :: Bool -> Empty ~> Bit
constant b = Circuit \BEmpty -> BBit <$> fresh (Constant b)

notGate :: Bit ~> Bit
notGate = Circuit \(BBit a) -> BBit <$> fresh (Not a)
andGate :: Bit ** Bit ~> Bit
andGate = Circuit \(BPair (BBit a) (BBit b)) -> BBit <$> fresh (And a b)
orGate :: Bit ** Bit ~> Bit
orGate = Circuit \(BPair (BBit a) (BBit b)) -> BBit <$> fresh (Or a b)
xorGate :: Bit ** Bit ~> Bit
xorGate = Circuit \(BPair (BBit a) (BBit b)) -> BBit <$> fresh (Xor a b)

-- | Select the second input when the first is true, and the third when it is false.
mux :: Bit ** Bit ** Bit ~> Bit
mux = Circuit \(BPair (BPair (BBit s) (BBit a)) (BBit b)) -> BBit <$> fresh (Mux s a b)

-- | A register's output starts at the given value. Each clock edge replaces it with its input
-- from the preceding cycle. All registers update simultaneously.
register :: Bool -> Bit ~> Bit
register initial = Circuit \(BBit a) -> BBit <$> fresh (Register initial a)

-- | A netlist with typed boundaries. Disconnected components are omitted.
type Netlist :: Wires -> Wires -> Type
data Netlist a b where
  Netlist :: (KnownWires a, KnownWires b) => Bundle a -> Bundle b -> IM.IntMap Driver -> Netlist a b

-- | Build a netlist, retaining precisely the components that can influence an output, including
-- through a register on a later cycle.
netlist :: Circuit a b -> Netlist a b
netlist (Circuit f) = Netlist ins outs (IM.restrictKeys ds (reachable IS.empty (ports outs)))
  where
    ((ins, outs), BuildState _ ds) = runBuild build (BuildState 0 IM.empty)
    build = do
      ins' <- freshBundle Input shape
      outs' <- f ins'
      pure (ins', outs')
    reachable seen [] = seen
    reachable seen (n : ns)
      | IS.member n seen = reachable seen ns
      | otherwise = reachable (IS.insert n seen) (inputs (ds IM.! n) ++ ns)

-- | A text netlist. Bit numbers are local to this netlist; bundle ports are ordered left to right.
renderNetlist :: Netlist a b -> String
renderNetlist (Netlist ins outs ds) =
  unlines $
    ["inputs " ++ show (ports ins), "outputs " ++ show (ports outs)]
      ++ [show n ++ " = " ++ show d | (n, d) <- IM.toAscList ds]

-- | A Graphviz graph of the same netlist used by the simulator. Register nodes show their
-- initial value. Copying is fan-out of an edge, and feedback aliases are small connection points.
toDot :: Netlist a b -> String
toDot (Netlist ins outs ds) =
  unlines $
    [ "digraph circuit {"
    , "rankdir=LR; bgcolor=transparent;"
    , "node [shape=box, style=rounded, fontname=Helvetica];"
    , "edge [fontname=Helvetica, fontsize=10];"
    ]
      ++ [wire n ++ " [shape=circle, label=\"in " ++ show i ++ "\"];" | (i, n) <- zip [0 :: Int ..] (ports ins), IM.member n ds]
      ++ ["{rank=same; " ++ unwords [wire n ++ ";" | (n, Register{}) <- IM.toAscList ds] ++ "}"]
      ++ ["{rank=sink; " ++ unwords ["o" ++ show i ++ ";" | i <- [0 .. length (ports outs) - 1]] ++ "}"]
      ++ concatMap draw (IM.toAscList ds)
      ++ concat
        [ ["o" ++ show i ++ " [shape=circle, label=\"out " ++ show i ++ "\"];", wire n ++ " -> o" ++ show i ++ ";"]
        | (i, n) <- zip [0 :: Int ..] (ports outs)
        ]
      ++ ["}"]
  where
    wire n = "w" ++ show n
    draw (_, Input) = []
    draw (n, d) =
      (wire n ++ " [" ++ attrs d ++ "];")
        : [ wire i ++ " -> " ++ wire n ++ " [headlabel=\"" ++ label ++ "\"" ++ layout d ++ "];"
          | (i, label) <- zip (inputs d) (portNames d)
          ]
    layout Register{} = ", constraint=false"
    layout _ = ""
    attrs (Alias _) = "shape=point, label=\"\""
    attrs (Register b _) = "shape=box, style=\"rounded,filled\", fillcolor=\"#dbeafe\", label=\"D " ++ bit b ++ "\""
    attrs d = "label=\"" ++ name d ++ "\""
    name (Constant b) = bit b
    name Not{} = "NOT"
    name And{} = "AND"
    name Or{} = "OR"
    name Xor{} = "XOR"
    name Mux{} = "MUX"
    name _ = ""
    bit False = "0"
    bit True = "1"
    portNames Mux{} = ["sel", "1", "0"]
    portNames Register{} = ["D"]
    portNames _ = repeat ""

-- | Verilog with scalar ports @in0@, @in1@, ... and @out0@, @out1@, ... in bundle order,
-- and a shared rising-edge clock @clk@. The caller supplies a valid Verilog module name.
-- Combinational cycles are rejected, and disconnected components are omitted.
--
-- Registers use @initial@ assignments to preserve their starting values in simulation;
-- synthesis support for initialization depends on the hardware target.
toVerilog :: String -> Netlist a b -> Either CircuitError String
toVerilog name graph@(Netlist ins outs ds) = do
  _ <- prepare graph
  pure $
    unlines $
      ["module " ++ name ++ "(" ++ List.intercalate ", " interface ++ ");"]
        ++ ["  " ++ declaration n d | (n, d) <- drivers]
        ++ ["  assign " ++ wire n ++ " = in" ++ show i ++ ";" | (i, n) <- inputPorts, IM.member n ds]
        ++ concatMap emit drivers
        ++ ["  assign out" ++ show i ++ " = " ++ wire n ++ ";" | (i, n) <- outputPorts]
        ++ ["endmodule"]
  where
    inputPorts = zip [0 :: Int ..] (ports ins)
    outputPorts = zip [0 :: Int ..] (ports outs)
    interface =
      ["input wire clk"]
        ++ ["input wire in" ++ show i | (i, _) <- inputPorts]
        ++ ["output wire out" ++ show i | (i, _) <- outputPorts]
    drivers = IM.toAscList ds
    wire n = "w" ++ show n
    declaration n Register{} = "reg " ++ wire n ++ ";"
    declaration n _ = "wire " ++ wire n ++ ";"
    emit (n, d) = case d of
      Input -> []
      Constant b -> assign (bit b)
      Not a -> assign ("~" ++ wire a)
      And a b -> assign (binary " & " a b)
      Or a b -> assign (binary " | " a b)
      Xor a b -> assign (binary " ^ " a b)
      Mux s a b -> assign (wire s ++ " ? " ++ wire a ++ " : " ++ wire b)
      Alias a -> assign (wire a)
      Register initial a ->
        [ "  initial " ++ wire n ++ " = " ++ bit initial ++ ";"
        , "  always @(posedge clk) " ++ wire n ++ " <= " ++ wire a ++ ";"
        ]
      where
        assign expression = ["  assign " ++ wire n ++ " = " ++ expression ++ ";"]
    binary op a b = wire a ++ op ++ wire b
    bit False = "1'b0"
    bit True = "1'b1"

-- | Bits participating in a combinational cycle. Every observable cycle must cross a register.
newtype CircuitError = CombinationalCycle [Int]
  deriving (Eq, Show)

-- | A circuit that passed combinational-cycle validation, carrying its current simulation state.
-- Composition and tensor preserve validity; unrestricted trace is available only before validation.
type Prepared :: CAT PREPARED
data Prepared a b where
  Prepared
    :: (KnownWires a, KnownWires b)
    => Simulator (Value @ Ready a) (Value @ Ready b) -> Prepared (Ready a) (Ready b)

instance CategoryOf PREPARED where
  type (~>) = Prepared
  type Ob a = (Is Ready a, KnownWires (UN Ready a))
instance Profunctor Prepared where
  dimap = dimapDefault
  r \\ Prepared{} = r
instance Promonad Prepared where
  id = Prepared id
  Prepared f . Prepared g = Prepared (f . g)
instance MonoidalProfunctor Prepared where
  one = Prepared one
  Prepared f ** Prepared g = Prepared (f ** g)
instance Monoidal PREPARED where
  type Unit = Ready Empty
  type a ** b = Ready (Pair (UN Ready a) (UN Ready b))
  withOb2 r = r
  leftUnitor = Prepared leftUnitor
  leftUnitorInv = Prepared leftUnitorInv
  rightUnitor = Prepared rightUnitor
  rightUnitorInv = Prepared rightUnitorInv
  associator = Prepared associator
  associatorInv = Prepared associatorInv
instance SymMonoidal PREPARED where
  swap = Prepared swap
instance (Ob a) => Comonoid (a :: PREPARED) where
  counit = Prepared counit
  comult = Prepared comult
instance (Ob a) => CocommutativeComonoid (a :: PREPARED)
instance CopyDiscard PREPARED

instance FunctorForRep Value where
  type Value @ Ready Bit = Sim Bool
  type Value @ Ready Empty = Sim ()
  type Value @ Ready (Pair a b) = Sim (Sample a, Sample b)
  fmap (Prepared machine) = machine

instance MonoidalProfunctor (Rep Value) where
  one = Rep one
  Rep f ** Rep g = Rep (f ** g)

-- | Cut the dependencies through registers and topologically order the combinational nodes.
-- Multiplexers depend on both data inputs, even when their selector is constant.
prepare :: Netlist a b -> Either CircuitError (Prepared (Ready a) (Ready b))
prepare (Netlist ins outs ds) = do
  order <- concat <$> traverse acyclic (stronglyConnComp [((n, d), n, deps d) | (n, d) <- IM.toAscList ds])
  let run state = Simulator \input ->
        let initial = IM.union (IM.fromList (inputValues ins input)) state
            evaluated = List.foldl' evaluate initial order
        in (output outs evaluated, run (IM.map (evaluated IM.!) registerInputs))
  pure (Prepared (run initialRegisters))
  where
    registers = IM.mapMaybe (\case Register b i -> Just (b, i); _ -> Nothing) ds
    initialRegisters = IM.map fst registers
    registerInputs = IM.map snd registers
    deps Register{} = []
    deps d = inputs d
    acyclic (AcyclicSCC (_, Input)) = Right []
    acyclic (AcyclicSCC (_, Register{})) = Right []
    acyclic (AcyclicSCC node) = Right [node]
    acyclic (CyclicSCC ns) = Left (CombinationalCycle (map fst ns))
    evaluate bs (n, d) = IM.insert n (value d) bs
      where
        get a = bs IM.! a
        value (Constant b) = b
        value (Not a) = not (get a)
        value (And a b) = get a && get b
        value (Or a b) = get a || get b
        value (Xor a b) = get a /= get b
        value (Mux s a b) = if get s then get a else get b
        value (Alias a) = get a
        value _ = get n

-- | Prepare a circuit once and simulate a sequence of clock cycles. Each output is observed
-- before the clock edge for the corresponding input.
simulate :: Circuit a b -> [Sample a] -> Either CircuitError [Sample b]
simulate circuit xs = do
  sim <- prepare (netlist circuit)
  pure (runSimulator (fmap @Value sim) xs) \\ sim
