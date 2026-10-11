{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Differentiable maps, compared at random points: arbitrary arrows are dense layers with a
-- @tanh@, and every reverse derivative is checked against finite differences.
module Props.Diff (test) where

import Control.Monad (replicateM)
import Data.Vector.Storable qualified as SV
import GHC.TypeNats (KnownNat)
import Test.Falsify (Property)
import Test.Falsify qualified as F
import Test.Falsify.Generator (Gen, elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (elem, fmap, id, mappend, (**), (.))

import Examples.Learning (scores)
import Proarrow.Category.Instance.Diff
  ( AsLens
  , DIFF (..)
  , Diff (..)
  , Forget
  , Point (..)
  , add
  , backward
  , bilinear
  , broadcast
  , coordinates
  , dot
  , forward
  , fromCoordinates
  , linear
  , matMat
  , pointwise
  , scale
  , softmax
  , softmaxCrossEntropy
  , split
  , times
  , pattern Vector
  )
import Proarrow.Category.Instance.Opposite (Op (..))
import Proarrow.Category.Instance.TensorNetwork (TNET (..), dimsOf, fromVector, matMul)
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.CopyDiscard (copy)
import Proarrow.Category.Monoidal.Hypergraph (cap)
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN, obj)
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object (KnownListOf)
import Proarrow.Optic.Lens (withLens)
import Proarrow.Profunctor.Representable (Rep)
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , check
  , genNamed
  , genP
  , genSomeDef
  , testEq
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Props.Hask ()

type R2 :: DIFF
type R2 = DF '[2]

type R3 :: DIFF
type R3 = DF '[3]

test :: TestTree
test =
  testGroup
    "Differentiable maps"
    [ testCategory @DIFF
    , testMonoidal_ @DIFF
    , testSymMonoidal_ @DIFF
    , testTerminalObject @DIFF
    , testBinaryProducts_ @DIFF
    , testCopyDiscard_ @DIFF
    , testCartesian_ @DIFF
    , testCommutativeMonoid_ @(DF '[2, 1])
    , testGroup
        "reverse derivatives are the transposed derivatives"
        [ testProperty "dense layers" (finiteDifferences @R2 @R3 =<< genNamed "f")
        , testProperty "composites" do
            f <- genNamed @(R2 ~> R3) "f"
            g <- genNamed @(R3 ~> R2) "g"
            finiteDifferences (g . f)
        , testProperty "linear maps" (finiteDifferences . linear =<< matrix @2 @3)
        , testProperty "tanh" (finiteDifferences (pointwise @3 tanh (\x -> 1 - tanh x ^ (2 :: Int))))
        , testProperty "times" (finiteDifferences (times @3))
        , testProperty "matrix times matrix" (finiteDifferences (matMat @2 @3 @4))
        , testProperty "matrix times matrix, large enough for BLAS" (finiteDifferences (matMat @16 @16 @16))
        , testProperty "broadcast" (finiteDifferences (broadcast @3 @4))
        , testProperty "softmax" (finiteDifferences (softmax @3 @2))
        , testProperty "softmax and cross-entropy" (finiteDifferences (softmaxCrossEntropy @3 @2))
        , testProperty "dot" (finiteDifferences (dot @3))
        , testProperty
            "a bilinear map, ik,jk->ij"
            (finiteDifferences (bilinear @'[2, 4] @'[3, 4] (scores @(TN '[2]) @(TN '[3]) @(TN '[4]))))
        , testProperty "copying adds the changes" do
            x <- genP @(Point '[3])
            dx <- genP @(Point '[3, 3])
            check "differs" (close (backward (copy @DIFF @R3) x dx) (forward (mappend @R3) dx))
        ]
    , testProperty "softmax gives each row probabilities that sum to 1" do
        z <- genP @(Point '[6])
        let p = coordinates (forward (softmax @3 @2) z)
        check
          ("gave " ++ show (SV.toList p))
          (SV.all (> 0) p && and [abs (SV.sum (SV.slice (3 * j) 3 p) - 1) < 1e-9 | j <- [0, 1]])
    , testProperty "the bilinear map of ik,jk->ij is a matrix times a transposed matrix" do
        p <- genP @(Point '[8, 12])
        let (Vector x, Vector y) = split @'[8] @'[12] p
        check
          "differs"
          ( close
              (forward (bilinear @'[2, 4] @'[3, 4] (scores @(TN '[2]) @(TN '[3]) @(TN '[4]))) p)
              (Vector (matMul False True 2 3 4 x y))
          )
    , testProperty "times is bilinear with the merging spider" do
        testEq "times" "times" (times @3) "bilinear mappend" (bilinear @'[3] @'[3] (mappend @(TN '[3])))
    , testProperty "matMat is bilinear with the cap on the summed index" do
        testEq
          "matMat"
          "matMat"
          (matMat @2 @3 @4)
          "bilinear (id ** cap ** id)"
          (bilinear @'[2, 3] @'[3, 4] ((obj @(TN '[2]) ** cap @(TN '[3])) ** obj @(TN '[4])))
    , testProfunctor @(Rep Forget)
    , testGroup
        "AsLens is a functor"
        [ testProperty "identity" do
            x <- genP @(Point '[2])
            dx <- genP @(Point '[2])
            check "differs" (sameLens (fmap @AsLens (id @_ @R2)) id x dx)
        , testProperty "composition, the chain rule" do
            f <- genNamed @(R2 ~> R3) "f"
            g <- genNamed @(R3 ~> R2) "g"
            x <- genP @(Point '[2])
            dz <- genP @(Point '[2])
            check "differs" (sameLens (fmap @AsLens (g . f)) (fmap @AsLens g . fmap @AsLens f) x dz)
        ]
    ]

-- | Two arrows of lenses agree on the view of a point and on the update of it with a change.
sameLens
  :: AsLens @ DF as ~> AsLens @ DF bs -> AsLens @ DF as ~> AsLens @ DF bs -> Point as -> Point bs -> Bool
sameLens (Op l) (Op l') x d = withLens l \get put -> withLens l' \get' put' ->
  close (get x) (get' x) && close (put (x, d)) (put' (x, d))

-- | A random linear map, as a tensor network.
matrix :: forall n m. (KnownNat n, KnownNat m) => Property ((TN '[n] :: TNET Double) ~> TN '[m])
matrix = fromVector . SV.fromList <$> F.gen (replicateM (product (dimsOf @'[n, m])) value)

-- | The reverse derivative at a random point, against the derivative from central differences: the
-- change of the input it gives, paired with a direction, is the change of the output along that
-- direction paired with the change of the output it was given.
finiteDifferences :: (a :: DIFF) ~> b -> Property ()
finiteDifferences f@Diff{} = do
  x <- genP
  v <- genP
  dy <- genP
  let h = 1e-5
      along s = forward f (add x (scale s v))
      derivative = scale (1 / (2 * h)) (add (along h) (scale (-1) (along (-h))))
  check "differs from finite differences" (abs (inner (backward f x dy) v - inner dy derivative) < 1e-6)

inner :: Point ns -> Point ns -> Double
inner x y = SV.sum (SV.zipWith (*) (coordinates x) (coordinates y))

-- | Whether two points are the same up to rounding.
close :: Point ns -> Point ns -> Bool
close p q = SV.length x == SV.length y && SV.and (SV.zipWith near x y)
  where
    (x, y) = (coordinates p, coordinates q)
    near a b = abs (a - b) <= 1e-9 * (1 + abs a + abs b)

-- | A small number, a multiple of a quarter.
value :: Gen Double
value = (/ 4) . fromIntegral <$> elem [-8 .. 8 :: Int]

instance Testable DIFF where
  showOb @a = show (dimsOf @(UN DF a))
  genSome = genSomeDef @'[DF '[], DF '[2], DF '[3], DF '[2, 1]]

instance (KnownListOf KnownNat ns) => TestableType (Point ns) where
  gen = GenNonEmpty (Point <$> traverse (\d -> SV.fromList <$> replicateM d value) (dimsOf @ns))

instance TestingEqShow (Point ns) where
  eqP l r = pure (close l r)
  showP (Point vs) = show (map SV.toList vs)

-- | A dense layer: a matrix and an offset on all the coordinates, and @tanh@.
instance (Ob (a :: DIFF), Ob b) => TestableType (Diff a b) where
  gen = GenNonEmpty do
    let (sa, sb) = (sum (dimsOf @(UN DF a)), sum (dimsOf @(UN DF b)))
    w <- SV.fromList <$> replicateM (sa * sb) value
    c <- SV.fromList <$> replicateM sb value
    pure (layer @(UN DF a) @(UN DF b) w c)

-- | The dense layer with the given matrix, row by row, and offset.
layer
  :: forall as bs
   . (KnownListOf KnownNat as, KnownListOf KnownNat bs) => SV.Vector Double -> SV.Vector Double -> DF as ~> DF bs
layer w c =
  Diff \x ->
    let y = SV.map tanh (preactivation (coordinates x))
    in (fromCoordinates y, \d -> fromCoordinates (transposed (SV.zipWith (\t dz -> dz * (1 - t * t)) y (coordinates d))))
  where
    sa = sum (dimsOf @as)
    sb = sum (dimsOf @bs)
    preactivation v = SV.generate sb \i -> c SV.! i + sum [w SV.! (i * sa + j) * v SV.! j | j <- [0 .. sa - 1]]
    transposed g = SV.generate sa \j -> sum [w SV.! (i * sa + j) * g SV.! i | i <- [0 .. sb - 1]]

instance (Ob (a :: DIFF), Ob b) => TestingEqShow (Diff a b) where
  eqP l r = do
    x <- genP
    dy <- genP
    pure (close (forward l x) (forward r x) && close (backward l x dy) (backward r x dy))
  showP _ = "<differentiable map>"

instance TestableProfunctor (Diff :: CAT DIFF)

instance TestableProfunctor (Rep Forget)
