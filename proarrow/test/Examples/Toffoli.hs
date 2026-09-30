{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | The Toffoli gate example from the @linear-smc@ library (the examples of /Evaluating Linear
-- Functions to Symmetric Monoidal Categories/), ported to "Proarrow.Tools.SMC": the Toffoli gate
-- as the usual circuit of Hadamard, T and controlled-not gates, written once and compiled to three
-- categories.
--
-- * In 'Mat', gates are complex matrices.
-- * In "Proarrow.Category.Instance.ZX", gates are spiders. They are not normalized, so the result
--   is compared with the Toffoli gate up to a scalar.
-- * In "Proarrow.Tools.Diagrams.Svg", gates are boxes, and the circuit is drawn.
--
-- The original's last controlled-not leaves its two control wires swapped, so its matrix is a
-- Toffoli gate followed by a swap of the controls. Here one more bind puts them back in order.
module Examples.Toffoli (test) where

import Data.Complex (Complex (..), cis, magnitude)
import Data.Foldable (toList)
import Data.Kind (Type)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Type.Nat (Nat1, Nat2)
import Data.Vec.Lazy (Vec (..))
import GHC.TypeNats qualified as TN
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, sum, (*), (**), (.))
import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Category.Instance.ZX (Bitstring (..), ZX (..))
import Proarrow.Category.Instance.ZX qualified as ZX
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Colimit.BinaryCoproduct (HasBiproducts (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), obj)
import Proarrow.Monoid (Comonoid (..))
import Proarrow.Testing (check)
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)
import Proarrow.Tools.SMC (Merge, SYN (..), Term, Union, lift, toSMC, (*))
import Proarrow.Tools.SMC qualified as SMC

-- * The circuit

-- | The gates the circuit is built from, for qubits @q@.
type Gates :: forall {k}. k -> Type
data Gates q = Gates
  { hadamardG :: q ~> q
  , tG :: q ~> q
  , tInvG :: q ~> q
  , cnotG :: q ** q ~> q ** q
  }

toffoliWith :: forall {k} (q :: k). (SymMonoidal k, Ob q) => Gates q -> q ** q ** q ~> q ** q ** q
toffoliWith gates = toSMC @(F q :** F q :** F q) \p -> SMC.do
  ((a0, b0), x0) <- p
  (a1, x1) <- cnot a0 (h x0)
  (b1, x2) <- cnot b0 (t' x1)
  (a2, x3) <- cnot a1 (t x2)
  (b2, x4) <- cnot b1 (t' x3)
  (b3, a3) <- cnot b2 (t a2)
  (b4, a4) <- cnot (t b3) (t' a3)
  a4 * b4 * h (t x4)
  where
    h, t, t' :: Term d g (F q) %1 -> Term d g (F q)
    h = lift (hadamardG gates)
    t = lift (tG gates)
    t' = lift (tInvG gates)
    cnot :: (Merge g1 g2) => Term d g1 (F q) %1 -> Term d g2 (F q) %1 -> Term d (Union g1 g2) (F q :** F q)
    cnot c x = lift (cnotG gates) (c * x)

-- | The same circuit written directly with the monoidal structure, for comparison. The wires are
-- @a ** b ** x@, and each two-qubit gate needs its two wires moved next to each other by hand.
toffoliManual :: forall {k} (q :: k). (SymMonoidal k, Ob q) => Gates q -> q ** q ** q ~> q ** q ** q
toffoliManual (Gates h t t' cnot) =
  onX (h . t)
    . onBA (cnot . (t ** t'))
    . onBA (cnot . (i ** t))
    . onBX (cnot . (i ** t'))
    . onAX (cnot . (i ** t))
    . onBX (cnot . (i ** t'))
    . onAX (cnot . (i ** h))
  where
    i = obj @q
    -- (a ** b) ** x to (a ** x) ** b, and back again, since all three wires are qubits
    shuffle :: q ** q ** q ~> q ** q ** q
    shuffle = associatorInv @k @q @q @q . (i ** swap @k @q @q) . associator @k @q @q @q
    onAX, onBX, onBA :: q ** q ~> q ** q -> q ** q ** q ~> q ** q ** q
    onAX f = shuffle . (f ** i) . shuffle
    onBX f = associatorInv @k @q @q @q . (i ** f) . associator @k @q @q @q
    onBA f = (swap @k @q @q ** i) . (f ** i) . (swap @k @q @q ** i)
    onX :: q ~> q -> q ** q ** q ~> q ** q ** q
    onX g = i ** i ** g

bools :: [Bool]
bools = [False, True]

-- * Matrices

type C = Complex Double

mat2 :: C -> C -> C -> C -> Mat (M Nat2 :: MatK C) (M Nat2)
mat2 a b c d = Mat ((a ::: b ::: VNil) ::: (c ::: d ::: VNil) ::: VNil)

-- | The gate @u@ controlled by a qubit: the identity when the control is off, @u@ when it is on.
ctrlMat :: forall (a :: MatK C). (Ob a) => Mat a a -> Mat (M Nat2 ** a) (M Nat2 ** a)
ctrlMat u = sum (mat2 1 0 0 0 ** obj @a) (mat2 0 0 0 1 ** u)

matGates :: Gates (M Nat2 :: MatK C)
matGates =
  Gates
    { hadamardG = mat2 s s s (-s)
    , tG = mat2 1 0 0 (cis (pi / 4))
    , tInvG = mat2 1 0 0 (cis (-(pi / 4)))
    , cnotG = ctrlMat (mat2 0 1 1 0)
    }
  where
    s = 1 / sqrt 2

toffoliMat :: Mat (M Nat2 ** M Nat2 ** M Nat2 :: MatK C) (M Nat2 ** M Nat2 ** M Nat2)
toffoliMat = toffoliWith matGates

ket :: Bool -> Mat (M Nat1 :: MatK C) (M Nat2)
ket b = Mat (((if b then 0 else 1) ::: VNil) ::: ((if b then 1 else 0) ::: VNil) ::: VNil)

-- | Equal up to rounding: the T gates are only approximately undone.
close :: Mat (a :: MatK C) b -> Mat a b -> Bool
close (Mat x) (Mat y) = and [magnitude (u - v) < 1e-9 | (u, v) <- zip (entries x) (entries y)]
  where
    entries = concatMap toList

-- * ZX

zxGates :: Gates (1 :: TN.Nat)
zxGates =
  Gates
    { hadamardG = ZX.hadamard
    , tG = ZX.zSpider (pi / 4)
    , tInvG = ZX.zSpider (-(pi / 4))
    , cnotG = ZX.cnot
    }

toffoliZX :: ZX 3 3
toffoliZX = toffoliWith zxGates

ketZ :: Bool -> ZX 0 1
ketZ b = ZX (Map.singleton (BS (fromEnum b), BS 0) 1)

ket3 :: Bool -> Bool -> Bool -> ZX 0 3
ket3 c1 c2 x = ketZ c1 ** ketZ c2 ** ketZ x

-- | The Toffoli gate, from its action on the basis states.
toffoliZXSpec :: ZX 3 3
toffoliZXSpec =
  foldr1
    addZX
    [ket3 c1 c2 (x /= (c1 && c2)) . dagger (ket3 c1 c2 x) | c1 <- bools, c2 <- bools, x <- bools]
  where
    addZX (ZX a) (ZX b) = ZX (Map.unionWith (+) a b)

-- | Equal up to a nonzero scalar, and up to rounding.
proportional :: ZX i o -> ZX i o -> Bool
proportional (ZX a) (ZX b) = case [(magnitude v, k) | (k, v) <- Map.toList b] of
  [] -> Map.null a
  entries ->
    let k0 = snd (maximum entries)
        c = at a k0 / at b k0
    in magnitude c > 1e-9 && and [magnitude (at a k - c P.* at b k) < 1e-9 | k <- Map.keys (Map.union a b)]
  where
    at m k = Map.findWithDefault 0 k m

-- * Pictures

-- | A qubit, as a wire of a string diagram.
type SQ = S '[Wire "q"]

-- | Gates as boxes. The controlled-not is drawn the way circuits draw it: a copy point on the
-- control joined to a box on the target.
svgGates :: Gates SQ
svgGates =
  Gates
    { hadamardG = node "H"
    , tG = node "T"
    , tInvG = node "T†"
    , cnotG = (obj @SQ ** node @'[Wire "q", Wire "q"] @'[Wire "q"] "⊕") . (comult @SQ ** obj @SQ)
    }

-- | The circuit, drawn.
toffoliPicture :: String
toffoliPicture = render (toffoliWith svgGates)

test :: TestTree
test =
  testGroup
    "Toffoli (Proarrow.Tools.SMC)"
    [ testProperty "controlled-not on the basis states (Mat)" $
        sequence_
          [ check (show (c, x)) (close (cnotG matGates . (ket c ** ket x)) (ket c ** ket (x /= c)))
          | c <- bools
          , x <- bools
          ]
    , testProperty "Toffoli on the basis states (Mat)" $
        sequence_
          [ check
              (show (c1, c2, x))
              (close (toffoliMat . (ket c1 ** ket c2 ** ket x)) (ket c1 ** ket c2 ** ket (x /= (c1 && c2))))
          | c1 <- bools
          , c2 <- bools
          , x <- bools
          ]
    , testProperty "written by hand, the same circuit (Mat)" $
        check "differs from toffoliWith" (close (toffoliManual matGates) toffoliMat)
    , testProperty "written by hand, the same circuit (ZX), up to a scalar" $
        check (show (toffoliManual zxGates)) (proportional (toffoliManual zxGates) toffoliZXSpec)
    , testProperty "Toffoli circuit (ZX), up to a scalar" $
        check (show toffoliZX) (proportional toffoliZX toffoliZXSpec)
    , testProperty "the circuit draws" $
        check "not an SVG document" ("<svg" `isInfixOf` toffoliPicture)
    ]
