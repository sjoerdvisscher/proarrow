{-# LANGUAGE QualifiedDo #-}

-- | Discrete probabilistic programs as string diagrams, after Peterseim and Lopuhaä-Zwakenberg,
-- /Fixed-Parameter Tractable Inference for Discrete Probabilistic Programs, via String Diagram
-- Algebraisation/ (LICS 2026). A program is a term over Boolean wires built from biased coins,
-- the connectives and @observe@, which keeps the runs in which a wire is true.
--
-- * In tensor networks a Boolean is a wire of dimension 2, a coin is the vector of its two
--   probabilities, the connectives are 0-1 matrices, and @observe@ picks out the entry for true.
--   Discarding a wire sums it out and copying a wire copies its value, so the program computes the
--   probability of each result together with the observations holding: running it is inference.
-- * Run as one network instead, with every building block a tensor on all its wires, the
--   read-back of open hypergraphs contracts the whole program in a planned order, as the paper's
--   algebraisation does, and gives the same probabilities.
-- * In string diagrams the same program is drawn, with a box for each coin and connective.
-- * Functions that call functions are evaluated once each and then combined, so a family of
--   programs whose probability of true is @2^-2^(n+1)@ costs linear time in @n@.
module Examples.Probabilistic (test, diseasePicture) where

import Data.Kind (Type)
import Data.List (isInfixOf)
import Data.Vector.Storable qualified as SV
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.OpenHypergraph (SIMPLIFY, Wires, prim, simplifyFlat)
import Proarrow.Category.Instance.TensorNetwork (TNET (..), fromEntries, toVector)
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Testing (check)
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)
import Proarrow.Tools.SMC (SYN (..), Term, lift, toSMC, unit, (**), (*^))
import Proarrow.Tools.SMC qualified as SMC

-- * Programs

-- | The building blocks of programs over Booleans @b@: a coin that is true with the given
-- probability, the connectives, and @observe@.
type Prims :: forall {k}. k -> Type
data Prims b = Prims
  { flipP :: Double -> Unit ~> b
  , andP :: b ** b ~> b
  , orP :: b ** b ~> b
  , notP :: b ~> b
  , observeP :: b ~> Unit
  }

-- | The connectives as terms.
andT
  , orT
    :: forall {k} (b :: k) d g1 g2
     . (Monoidal k, Ob b, SMC.Merge g1 g2)
    => Prims b -> Term d g1 (F b) -> Term d g2 (F b) -> Term d (SMC.Union g1 g2) (F b)
andT p x y = lift @(F b :** F b) @(F b) (andP p) (x ** y)
orT p x y = lift @(F b :** F b) @(F b) (orP p) (x ** y)

notT :: forall {k} (b :: k) d g. (Monoidal k, Ob b) => Prims b -> Term d g (F b) -> Term d g (F b)
notT p = lift @(F b) @(F b) (notP p)

-- | A program without inputs as a term: a call of it.
call :: forall {k} (b :: k) d. (Monoidal k, Ob b) => (Unit ~> b) -> Term d '[] (F b)
call f = lift @I @(F b) f unit

-- | A coin that is true with the given probability.
coin :: (Monoidal k, Ob (b :: k)) => Prims b -> Double -> Term d '[] (F b)
coin p q = call (flipP p q)

-- | The test of the paper's running example on a patient: positive with probability 0.99 when the
-- patient has the disease, and with probability 0.02 when not. Each call flips its own coins.
diseaseTest :: forall {k} (b :: k). (CopyDiscard k, Ob b) => Prims b -> b ~> b
diseaseTest p = toSMC @(F b) @(F b) \z -> orT p (andT p z (coin p 0.99)) (andT p (notT p z) (coin p 0.02))

-- | Whether a patient has the disease, which one in ten thousand have, given one positive and one
-- negative test.
hasDisease :: forall {k} (b :: k). (CopyDiscard k, Ob b) => Prims b -> Unit ~> b
hasDisease p = toSMC @I @(F b) \() -> SMC.do
  x <- coin p 1e-4
  let t = lift @(F b) @(F b) (diseaseTest p)
  lift @(F b) @I (observeP p) (andT p (t x) (notT p (t x))) *^ x

-- | A family of programs: @f 0@ is the conjunction of two fair coins, and @f (n + 1)@ the
-- conjunction of two calls of @f n@, so it is true with probability @2^-2^(n+1)@. Each @f n@ is a
-- function of its own, compiled once and called twice.
family :: forall {k} (b :: k). (CopyDiscard k, Ob b) => Prims b -> Int -> Unit ~> b
family p 0 = toSMC @I @(F b) \() -> andT p (coin p 0.5) (coin p 0.5)
family p n = let f = family p (n - 1) in toSMC @I @(F b) \() -> andT p (call f) (call f)

-- * Inference

-- | A Boolean as a wire of dimension 2: false, then true.
type Bit :: TNET Double
type Bit = TN '[2]

-- | The building blocks as tensor networks.
tensors :: Prims Bit
tensors =
  Prims
    { flipP = \q -> fromEntries [[1 - q], [q]]
    , andP = fromEntries [[1, 1, 1, 0], [0, 0, 0, 1]]
    , orP = fromEntries [[1, 0, 0, 0], [0, 1, 1, 1]]
    , notP = fromEntries [[0, 1], [1, 0]]
    , observeP = fromEntries [[0, 1]]
    }

-- | The building blocks as boxes of open hypergraphs, to run a whole program as one network.
boxedTensors :: Prims (Wires '[Bit] :: SIMPLIFY (TNET Double))
boxedTensors =
  Prims
    { flipP = \q -> prim (Str (flipP tensors q))
    , andP = prim (Str (andP tensors))
    , orP = prim (Str (orP tensors))
    , notP = prim (Str (notP tensors))
    , observeP = prim (Str (observeP tensors))
    }

-- | A program run as one network of tensors, each box bent into a state on all its wires, and
-- contracted in the order of 'Proarrow.Tools.ContractionOrder.planContraction', as the paper's
-- algebraisation does.
asNetwork :: (Unit ~> (Wires '[Bit] :: SIMPLIFY (TNET Double))) -> Unit ~> Bit
asNetwork f = unStr (simplifyFlat f)

-- | The probability of each result of a program together with its observations holding.
probabilities :: (Unit ~> Bit) -> (Double, Double)
probabilities f = let v = toVector f in (v SV.! 0, v SV.! 1)

-- * Pictures

-- | A Boolean as a wire of a string diagram.
type SB = S '[Wire "𝔹"]

-- | The building blocks as boxes.
boxes :: Prims SB
boxes =
  Prims
    { flipP = node . show
    , andP = node "∧"
    , orP = node "∨"
    , notP = node "¬"
    , observeP = node "observe"
    }

-- | The running example, drawn.
diseasePicture :: String
diseasePicture = render (hasDisease boxes)

test :: TestTree
test =
  testGroup
    "Probabilistic programs"
    [ testProperty "inference gives the probability of each answer together with the observations" do
        let (healthy, ill) = probabilities (hasDisease tensors)
            prior = 1e-4
            expectedIll = prior * 0.99 * 0.01
            expectedHealthy = (1 - prior) * 0.02 * 0.98
        check ("found " ++ show (healthy, ill)) (abs (ill - expectedIll) < 1e-15 && abs (healthy - expectedHealthy) < 1e-15)
    , testProperty "run as one network of tensors, contracted in a planned order, it gives the same" do
        let (healthy, ill) = probabilities (hasDisease tensors)
            (healthy', ill') = probabilities (asNetwork (hasDisease boxedTensors))
        check ("found " ++ show (healthy', ill')) (abs (healthy - healthy') < 1e-15 && abs (ill - ill') < 1e-15)
    , testProperty "the nested family is true with doubly exponentially small probability" do
        let (_, true5) = probabilities (family tensors 5)
            (_, true1000) = probabilities (family tensors 1000)
        check ("found " ++ show true5) (true5 == 2 ^^ (-64 :: Int))
        -- each member is evaluated once, so even the thousandth is quick; its probability underflows
        check ("found " ++ show true1000) (true1000 == 0)
    , testProperty "the running example draws" do
        check "not an SVG document" ("<svg" `isInfixOf` diseasePicture)
    ]
