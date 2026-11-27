-- | ZX diagrams, circuit construction, and their matrix interpretation.
module Examples.ZXRewrite.Diagram where

import Control.Monad (unless)
import Data.Bifunctor (bimap)
import Data.Complex (Complex, mkPolar)
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as Map
import Data.Ratio (denominator)
import GHC.TypeNats (Nat)
import System.Random (mkStdGen, uniformR)
import Test.Falsify (Property, testFailed)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.OpenHypergraph (W1, W2)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.ZX qualified as ZX
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Object (ListOf (..), withKnownListOf)
import Proarrow.Testing (check)

-- Phases are rational multiples of pi, normalised modulo 2 at construction.
data Colour = Z | X deriving (Eq, Ord, Show)

-- Scalar power angle denotes sqrt(2)^power * exp(i*pi*angle).
-- Selected and Pivot mark the spiders of one explicitly requested expansion.
data Generator a = Spider Colour a | Hadamard | Scalar Int Rational | Selected a | Pivot Bool a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Diagram = HG.OPENHG () (Generator Rational)
type Q = HG.Wires W1 :: Diagram
type QQ = HG.Wires W2 :: Diagram
type SomeDiagram = HG.SomeHypergraph () (Generator Rational)

phase :: Rational -> Rational
phase a = a - 2 * fromInteger (floor (a / 2))

spider
  :: forall as bs. (HG.SortList as, HG.SortList bs) => Colour -> Rational -> (HG.Wires as :: Diagram) ~> HG.Wires bs
spider c a = HG.box (Spider c (phase a))

h :: Q ~> Q
h = HG.box Hadamard

z, x :: Rational -> Q ~> Q
z = spider Z
x = spider X

-- Like the existing ZX.cnot, this uses unnormalised spiders: the diagram
-- denotes CNOT / sqrt 2. We retain this scalar throughout simplification.
cnot :: QQ ~> QQ
cnot = (obj @Q ** spider @W2 @W1 X 0) . (spider @W1 @W2 Z 0 ** obj @Q)

-- A gate list keeps generation independent of diagram construction. Qubits
-- are numbered left to right; phases are rational multiples of pi.
data CircuitGate = CNot Int Int | Had Int | ZPhase Int Rational
  deriving (Eq, Show)

-- The default PyZX CNOT_HAD_PHASE distribution: 60% CNOT, 20% H, 20% T.
-- Depth counts gates, not parallel layers. Seeds are reproducible with random's
-- StdGen; they do not reproduce Python's random.Random sequences.
cnotHadPhaseCircuit :: Int -> Int -> Int -> Either String [CircuitGate]
cnotHadPhaseCircuit qubits depth seed = do
  unless (qubits >= 2) (Left "cnotHadPhaseCircuit: need at least two qubits")
  unless (depth >= 0) (Left "cnotHadPhaseCircuit: negative gate count")
  pure (go depth (mkStdGen seed))
  where
    go 0 _ = []
    go remaining rng =
      let (kind, rng1) = uniformR (0 :: Int, 4) rng
          (q, rng2) = uniformR (0, qubits - 1) rng1
          (other, rng3) = uniformR (0, qubits - 2) rng2
          target = if other < q then other else other + 1
          (gate, next) = case kind of
            4 -> (Had q, rng2)
            3 -> (ZPhase q (1 / 4), rng2)
            _ -> (CNot q target, rng3)
      in gate : go (remaining - 1) next

-- Build the circuit wiring directly, keeping the frontier in qubit order.
-- Each CNOT adds sqrt(2): our unnormalised Z/X spider pair alone denotes
-- CNOT/sqrt(2). The generated circuit therefore has ordinary unitary semantics.
circuitDiagram :: Int -> [CircuitGate] -> Either String SomeDiagram
circuitDiagram qubits gates = do
  unless (qubits >= 0) (Left "circuitDiagram: negative qubit count")
  let validQ q = q >= 0 && q < qubits
      valid (CNot c t) = validQ c && validQ t && c /= t
      valid (Had q) = validQ q
      valid (ZPhase q _) = validQ q
  unless (all valid gates) (Left "circuitDiagram: invalid gate qubit")
  let step (next, frontier, boxes, power) gate = case gate of
        CNot c t ->
          ( next + 3
          , IM.insert c next (IM.insert t (next + 1) frontier)
          , HG.Box (Spider X 0) [next + 2, frontier IM.! t] [next + 1]
              : HG.Box (Spider Z 0) [frontier IM.! c] [next, next + 2]
              : boxes
          , power + 1
          )
        Had q -> (next + 1, IM.insert q next frontier, HG.Box Hadamard [frontier IM.! q] [next] : boxes, power)
        ZPhase q p -> (next + 1, IM.insert q next frontier, HG.Box (Spider Z (phase p)) [frontier IM.! q] [next] : boxes, power)
      (end, outputs, built, cnots) = foldl' step (qubits, IM.fromList [(i, i) | i <- [0 .. qubits - 1]], [], 0) gates
  pure
    (someDiagram end [0 .. qubits - 1] (IM.elems outputs) (reverse built ++ [HG.Box (Scalar cnots 0) [] [] | cnots /= 0]))

data DiagramSize = DiagramSize {sizeSpiders :: Int, sizeHadamards :: Int, sizeNonClifford :: Int}
  deriving (Eq, Show)

diagramSize :: (a :: Diagram) ~> b -> DiagramSize
diagramSize graph =
  let (_, _, _, boxes) = HG.hypergraphParts graph
  in DiagramSize
       (length [() | HG.Box Spider{} _ _ <- boxes])
       (length [() | HG.Box Hadamard _ _ <- boxes])
       (length [() | HG.Box (Spider _ p) _ _ <- boxes, nonClifford p])

sorts :: Int -> [HG.SomeSort ()]
sorts n = concat (replicate n (HG.sortList @() @W1))

ports :: HG.Box l n -> [n]
ports (HG.Box _ is os) = is ++ os

-- Every symbolic box is bent into a state. ZX spiders and the Hadamard tensor
-- are symmetric, so this forgets port direction without changing the semantics.
stateBox :: HG.Box l n -> HG.Box l n
stateBox (HG.Box l is os) = HG.Box l [] (is ++ os)

-- An open graph encoded as explicit Z spiders and Hadamard boxes. Each graph
-- edge gets two distinct wire nodes, one at each end of its Hadamard box.
-- The first vertices have output wires. The remaining vertices are internal.
openGraph :: Int -> [Rational] -> [(Int, Int)] -> SomeDiagram
openGraph boundary phases edges =
  let endpoint k side = boundary + 2 * k + side
      incident i = concat [[endpoint k 0 | i == a] ++ [endpoint k 1 | i == b] | (k, (a, b)) <- zip [0 ..] edges]
      boxes =
        [HG.Box (Spider Z (phase p)) [] ([i | i < boundary] ++ incident i) | (i, p) <- zip [0 ..] phases]
          ++ [HG.Box Hadamard [] [endpoint k 0, endpoint k 1] | k <- [0 .. length edges - 1]]
  in HG.reifySorts (sorts boundary) \ @bs ->
       HG.SomeHypergraph
         (HG.unsafeOpenHypergraph @_ @'[] @bs (sorts (boundary + 2 * length edges)) [] [0 .. boundary - 1] boxes)

nonClifford :: Rational -> Bool
nonClifford p = denominator (2 * phase p) /= 1

spiderCount :: (a :: Diagram) ~> b -> Int
spiderCount diagram = let (_, _, _, boxes) = HG.hypergraphParts diagram in length [() | HG.Box Spider{} _ _ <- boxes]

-- Interpret explicit spiders using the existing matrix ZX category. The
-- read-back contracts the tensors, including closed components and scalars.
-- A degree-n spider is a phase state followed by n-legged copying in its basis.
spiderTensor :: Colour -> Rational -> Int -> HG.SomeArrow Nat
spiderTensor c p n = fanout n \ys f ->
  HG.SomeArrow Nil ys (f . Str (case c of Z -> ZX.zSpider (pi * fromRational p); X -> ZX.xSpider (pi * fromRational p)))
  where
    fanout :: Int -> (forall ys. (HG.SortList ys) => HG.Sorts ys -> ('[1] ~> ys) -> r) -> r
    fanout 0 k = k Nil (Str (case c of Z -> ZX.zSpider 0; X -> ZX.xSpider 0))
    fanout degree k = fanout (degree - 1) \ys f ->
      withKnownListOf ys $
        k (Cons @1 ys) ((obj @'[1] ** f) . Str (case c of Z -> ZX.zCopy; X -> ZX.xCopy))

matrix :: (a :: Diagram) ~> b -> Either String (Map.Map (Int, Int) (Complex Double))
matrix graph =
  let (ns, is, os, bs) = HG.hypergraphParts graph
      qubits n = concat (replicate n (HG.sortList @Nat @'[1]))
      primitive (HG.Box l ins outs) = HG.Box (HG.unsafePrim (tensor l (length ins + length outs))) [] (ins ++ outs)
      tensor Hadamard _ = HG.someArrow @'[] @'[1, 1] (Str ((obj @1 ** ZX.hadamard @1) . ZX.zSpider 0))
      tensor (Spider c p) n = spiderTensor c p n
      tensor (Selected p) n = spiderTensor Z p n
      tensor (Pivot _ p) n = spiderTensor Z p n
      tensor (Scalar power angle) _ =
        HG.someArrow @'[] @'[]
          (Str (ZX.ZX (Map.singleton (0, 0) (mkPolar (sqrt 2 ^^ power) (pi * fromRational angle))) :: ZX.ZX 0 0))
  in HG.reifySorts (qubits (length is)) \ @as ->
       HG.reifySorts (qubits (length os)) \ @bs -> do
         arrow <-
           HG.simplify
             (HG.frobeniusWith (const 2))
             (HG.unsafeOpenHypergraph @_ @as @bs (qubits (length ns)) is os (map primitive bs))
         pure (matrixEntries (unStr arrow))

boxCount :: (a :: Diagram) ~> b -> Int
boxCount graph = let (_, _, _, bs) = HG.hypergraphParts graph in length bs

scalarFactors :: (a :: Diagram) ~> b -> (Int, Rational)
scalarFactors graph =
  let (_, _, _, boxes) = HG.hypergraphParts graph
  in (sum [power | HG.Box (Scalar power _) _ _ <- boxes], phase (sum [angle | HG.Box (Scalar _ angle) _ _ <- boxes]))

-- Boundary lists remain ordered even when their node references repeat.
someDiagram :: Int -> [Int] -> [Int] -> [HG.Box (Generator Rational) Int] -> SomeDiagram
someDiagram n ins outs boxes =
  HG.reifySorts (sorts (length ins)) \ @as ->
    HG.reifySorts (sorts (length outs)) \ @bs ->
      HG.SomeHypergraph (HG.unsafeOpenHypergraph @_ @as @bs (sorts n) ins outs boxes)

matrixEntries :: ZX.ZX i o -> Map.Map (Int, Int) (Complex Double)
matrixEntries (ZX.ZX m) = Map.mapKeys (bimap fromEnum fromEnum) m

sameMatrix :: Map.Map (Int, Int) (Complex Double) -> Map.Map (Int, Int) (Complex Double) -> Bool
sameMatrix a b = all ZX.isZero (Map.elems (Map.unionWith (+) a (Map.map negate b)))

checkMatrix :: (a :: Diagram) ~> b -> Map.Map (Int, Int) (Complex Double) -> Property ()
checkMatrix graph expected = case matrix graph of
  Left err -> testFailed err
  Right actual -> check "matrix matches existing ZX semantics" (sameMatrix expected actual)
