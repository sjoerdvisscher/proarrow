{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoStarIsType #-}

-- | Learning with differentiable maps: a model is a parametrised arrow of
-- "Proarrow.Category.Instance.Diff", written with "Proarrow.Tools.SMC", its loss is the model
-- followed by the squared error, and the reverse derivative of the loss gives the gradient of the
-- parameters. An optimiser is a lens onto the parameters in its state, as in Cruttwell, Gavranović,
-- Ghani, Wilson and Zanasi, /Categorical Foundations of Gradient-Based Learning/: its view gives
-- the parameters and its update takes the gradient to the next state, which for momentum also
-- holds a velocity.
--
-- The models work on batches: a batch of @b@ inputs is a matrix with the inputs as its rows, and the
-- loss of a batch is the sum of the losses of its samples, so its gradient adds up theirs. A layer's
-- weights are a matrix from its inputs to its outputs, with a row for each input.
--
-- * Linear regression recovers the coefficients of a linear function from its values.
-- * A perceptron with one hidden layer learns exclusive or, which no linear model can, and with
--   momentum it does so in far fewer passes.
-- * A classifier with a softmax output tells apart three rings of points around the origin,
--   trained with the cross-entropy, and classifies points of the rings it has not seen.
-- * Self-attention learns to give every position of a sequence its largest value, by weighting the
--   positions with the softmax of query and key scores. The scores are a bilinear map, given as a
--   tensor network.
module Examples.Learning (test, scores, attentionPicture, attentionWiringPicture) where

import Data.Kind (Type)
import Data.List (isInfixOf)
import Data.Vector.Storable qualified as SV
import GHC.TypeNats (KnownNat, Nat, type (*))
import Test.Falsify (Property)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, mappend, (**), (.))

import Proarrow.Category.Instance.Diff
  ( DIFF (..)
  , Point (..)
  , add
  , append
  , backward
  , bilinear
  , broadcast
  , coordinates
  , forward
  , fromCoordinates
  , matMat
  , pointwise
  , scale
  , softmax
  , softmaxCrossEntropy
  , split
  , zero
  , pattern Vector
  )
import Proarrow.Category.Instance.Diff qualified as Diff
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.TensorNetwork (TNET (..), dimsOf)
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius)
import Proarrow.Category.Monoidal.Strength (first')
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object (KnownListOf)
import Proarrow.Optic.Lens (Lens', lens, withLens)
import Proarrow.Promonad.Reader (Reader (..))
import Proarrow.Testing (check)
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)
import Proarrow.Tools.SMC (SYN (..), Term, delta, lift, toSMC, (**), (*^))
import Proarrow.Tools.SMC qualified as SMC

type R1 :: DIFF
type R1 = DF '[1]

type R2 :: DIFF
type R2 = DF '[2]

type R3 :: DIFF
type R3 = DF '[3]

type R4 :: DIFF
type R4 = DF '[4]

-- | A batch of @b@ vectors of dimension @n@, the rows of a matrix.
type Batch :: Nat -> Nat -> DIFF
type Batch n b = DF '[b * n]

-- | An arrow from @a@ to @b@ with a parameter @x@, @x ** a ~> b@.
type Para :: forall {k}. k -> k +-> k
type Para x = Reader (OP x)

-- * Building blocks

-- | The sum of two terms.
plus
  :: forall n d g1 g2
   . (KnownNat n, SMC.Merge g1 g2)
  => Term d g1 (F (DF '[n])) -> Term d g2 (F (DF '[n])) -> Term d (SMC.Union g1 g2) (F (DF '[n]))
plus a b = lift mappend (a ** b)

-- | The dot product of two terms.
dot
  :: forall n d g1 g2
   . (KnownNat n, SMC.Merge g1 g2) => Term d g1 (F (DF '[n])) -> Term d g2 (F (DF '[n])) -> Term d (SMC.Union g1 g2) (F R1)
dot a b = lift (Diff.dot @n) (a ** b)

-- | @tanh@ on each coordinate of a term.
tanhT :: (KnownNat n) => Term d g (F (DF '[n])) -> Term d g (F (DF '[n]))
tanhT = lift (pointwise tanh \x -> 1 - tanh x * tanh x)

-- * Training

-- | Weights from @n@ inputs to @m@ outputs applied to each of a batch of vectors.
layer
  :: forall m n b d g1 g2
   . (KnownNat m, KnownNat n, KnownNat b, KnownNat (n * m), KnownNat (b * n), KnownNat (b * m), SMC.Merge g1 g2)
  => Term d g1 (F (Batch n b)) -> Term d g2 (F (DF '[n * m])) -> Term d (SMC.Union g1 g2) (F (Batch m b))
layer x w = lift (matMat @b @n @m) (x ** w)

-- | An affine layer on a batch of vectors: weights from @n@ inputs to @m@ outputs applied to each vector, plus
-- an offset.
affineLayer
  :: forall m n b d g1 g2 g3
   . ( KnownNat m
     , KnownNat n
     , KnownNat b
     , KnownNat (n * m)
     , KnownNat (b * n)
     , KnownNat (b * m)
     , SMC.Merge g1 g2
     , SMC.Merge (SMC.Union g1 g2) g3
     )
  => Term d g1 (F (Batch n b))
  -> Term d g2 (F (DF '[n * m]))
  -> Term d g3 (F (DF '[m]))
  -> Term d (SMC.Union (SMC.Union g1 g2) g3) (F (Batch m b))
affineLayer x w c = plus (layer @m @n @b x w) (lift (broadcast @m @b) c)

-- | The sum of the squared differences of predictions and targets.
squaredError :: forall n. (KnownNat n) => DF '[n] ** DF '[n] ~> R1
squaredError = toSMC @(F (DF '[n]) :** F (DF '[n])) \(prediction, target) -> SMC.do
  d <- plus prediction (lift (pointwise negate (const (-1))) target)
  dot d d

-- | The loss of a model on a batch, inputs and targets: the model, with the targets passed
-- alongside by its strength, followed by the given error of its outputs against the targets.
loss
  :: forall p a n. (Ob p, Ob a, KnownNat n) => DF '[n] ** DF '[n] ~> R1 -> Para p a (DF '[n]) -> Para p (a ** DF '[n]) R1
loss err model = rmap err (first' @(DF '[n]) model)

-- | Samples of an input and a target, in batches of @b@: the inputs as the rows of a matrix, and the
-- targets as the rows of another. Samples that do not fill a batch are left out.
batches :: forall n k b. (KnownNat b) => [Point '[n, k]] -> [Point '[b * n, b * k]]
batches samples = case splitAt b samples of
  (chunk, rest) | length chunk == b -> batch chunk : batches @n @k @b rest
  _ -> []
  where
    b = sum (dimsOf @'[b])
    batch chunk = let (xs, ts) = unzip [(x, t) | Point [x, t] <- chunk] in Point [SV.concat xs, SV.concat ts]

-- | The change of the parameters that increases the loss fastest, at a sample.
gradient
  :: forall ps as
   . (KnownListOf KnownNat ps, KnownListOf KnownNat as) => Para (DF ps) (DF as) R1 -> Point ps -> Point as -> Point ps
gradient (Reader f) w x = fst (split @ps @as (backward f (append w x) (Vector (SV.singleton 1))))

-- | The outputs of a model with the given parameters.
predict :: Para (DF ps) (DF as) (DF bs) -> Point ps -> Point as -> Point bs
predict (Reader f) w x = forward f (append w x)

-- | An optimiser: a lens onto the parameters in its state. Its view gives the parameters to run
-- the model with, and its update takes the gradient there to the next state.
type Optimiser :: Type -> [Nat] -> Type
type Optimiser s ps = Lens' s (Point ps)

-- | Gradient descent with the given rate: the state is the parameters, and an update moves them
-- against the gradient.
gradientDescent :: Double -> Optimiser (Point ps) ps
gradientDescent rate = lens id \(w, dw) -> add w (scale (negate rate) dw)

-- | Gradient descent with momentum: the state also keeps a velocity, which each update decays by
-- the given factor and adds the gradient to, and the parameters move against the velocity.
momentum :: Double -> Double -> Optimiser (Point ps, Point ps) ps
momentum rate decay = lens snd \((v, w), dw) ->
  let v' = add (scale decay v) dw in (v', add w (scale (negate rate) v'))

-- | Training: one update of the optimiser for each batch, for the given number of passes over the
-- batches. The parameters of each update are computed before the next one starts, so that no chain
-- of unevaluated updates builds up.
train
  :: (KnownListOf KnownNat ps, KnownListOf KnownNat as)
  => Optimiser s ps -> Int -> Para (DF ps) (DF as) R1 -> s -> [Point as] -> s
train optimiser passes f start bs = withLens optimiser \params update ->
  let step st x = let st' = update (st, gradient f (params st) x) in foldr seq () (vectors (params st')) `seq` st'
      go 0 st = st
      go k st = go (k - 1) (foldl' step st bs)
  in go passes start

-- * Linear regression

-- | A linear function of three inputs, on a batch: weights, an offset and the inputs.
affine :: forall b. (KnownNat b, KnownNat (b * 3)) => Para (DF '[3, 1]) (Batch 3 b) (DF '[b])
affine = Reader (toSMC @(F R3 :** F R1 :** F (Batch 3 b)) \(w, c, x) -> affineLayer @1 @3 @b x w c)

-- | Samples of @x - 2y + z/2 + 0.3@ on a grid.
regressionSamples :: [Point '[3, 1]]
regressionSamples =
  [ Point [SV.fromList [x, y, z], SV.singleton (x - 2 * y + z / 2 + 0.3)]
  | x <- [-1, 0, 1]
  , y <- [-1, 0, 1]
  , z <- [-1, 0, 1]
  ]

-- * Exclusive or

-- | A hidden layer of two @tanh@ units and a @tanh@ output, on a batch: the hidden weights and
-- offsets, the output weights and offset, and the inputs.
perceptron :: forall b. (KnownNat b, KnownNat (b * 2)) => Para (DF '[4, 2, 2, 1]) (Batch 2 b) (DF '[b])
perceptron =
  Reader
    ( toSMC @(F R4 :** F R2 :** F R2 :** F R1 :** F (Batch 2 b)) \(w1, b1, w2, b2, x) -> SMC.do
        h <- tanhT (affineLayer @2 @2 @b x w1 b1)
        tanhT (affineLayer @1 @2 @b h w2 b2)
    )

-- | Exclusive or on -1 and 1.
xorSamples :: [Point '[2, 1]]
xorSamples = [Point [SV.fromList [x, y], SV.singleton (if x == y then -1 else 1)] | x <- [-1, 1], y <- [-1, 1]]

-- | All of exclusive or as one batch.
xorBatch :: [Point '[4 * 2, 4]]
xorBatch = batches @2 @1 @4 xorSamples

-- | Small weights that tell the two hidden units apart.
xorStart :: Point '[4, 2, 2, 1]
xorStart = Point [SV.fromList [0.5, 0.3, -0.4, 0.6], SV.fromList [0.1, -0.1], SV.fromList [0.7, -0.5], SV.singleton 0]

-- * Three rings

-- | Scores for three classes from two coordinates, on a batch: a hidden layer of eight @tanh@ units,
-- with its weights and offsets, and the output weights and offsets.
classifier
  :: forall b
   . (KnownNat b, KnownNat (b * 2), KnownNat (b * 8), KnownNat (b * 3)) => Para (DF '[16, 8, 24, 3]) (Batch 2 b) (Batch 3 b)
classifier =
  Reader
    ( toSMC @(F (DF '[16]) :** F (DF '[8]) :** F (DF '[24]) :** F (DF '[3]) :** F (Batch 2 b)) \(w1, b1, w2, b2, x) -> SMC.do
        h <- tanhT (affineLayer @8 @2 @b x w1 b1)
        affineLayer @3 @8 @b h w2 b2
    )

-- | Points on three rings around the origin, of radius about 0.3, 0.6 and 0.9, each with its ring as
-- a target that puts all probability on it. The @i@th point is on ring @i `mod` 3@, at @i@ times the
-- golden angle, so that the rings take turns and the points spread around them.
rings :: [Int] -> [Point '[2, 3]]
rings is =
  [ Point [SV.fromList [r * cos a, r * sin a], SV.generate 3 \c' -> if c' == c then 1 else 0]
  | i <- is
  , let c = i `mod` 3
        a = fromIntegral i * 2.39996
        r = 0.3 * fromIntegral (c + 1) + 0.05 * sin (fromIntegral i * 1.7)
  ]

-- | Small weights of both signs.
classifierStart :: Point '[16, 8, 24, 3]
classifierStart = fromCoordinates (SV.generate (sum (dimsOf @'[16, 8, 24, 3])) \i -> 0.5 * sin (fromIntegral (i * i + 1)))

-- | The share of the points that the classifier with the given parameters puts on their ring.
accuracy :: Point '[16, 8, 24, 3] -> [Point '[2, 3]] -> Double
accuracy w samples = fromIntegral (length (filter id hits)) / fromIntegral (length hits)
  where
    hits =
      [ SV.maxIndex (coordinates (predict (classifier @1) w x)) == SV.maxIndex t
      | (x, Vector t) <- map (split @'[2] @'[3]) samples
      ]

-- * Attention

-- | The wiring of @ik,jk->ij@: two matrices to the first times the transposed second, the scores
-- of each query against each key. It is all spiders, so it works with any index objects that are
-- Frobenius algebras: tensor networks for training, and string diagrams for drawing.
scores
  :: forall {c} (i :: c) j k
   . (SymMonoidal c, Frobenius k, Ob i, Ob j)
  => i ** k ** j ** k ~> i ** j
scores = toSMC @(F i :** F k :** F j :** F k) \(a, b, c, d) -> delta b d *^ (a ** c)

-- | The steps of single-head self-attention over a sequence @x@: projecting it with weights @w@ to
-- queries, keys or values @s@, weighing each query against each key, @a@, mixing the values with
-- those weights, and an output map with weights @wo@ to the result @o@.
type AttentionSteps :: forall {c}. c -> c -> c -> c -> c -> c -> Type
data AttentionSteps x w s a wo o = AttentionSteps
  { project :: x ** w ~> s
  , weigh :: s ** s ~> a
  , mix :: a ** s ~> s
  , output :: s ** wo ~> o
  }

-- | Single-head self-attention from its steps: the queries, keys and values are the sequence projected
-- with their own weights, the keys weigh the queries, and the weighted values go through the output
-- map. The parameters are the query, key, value and output weights.
attentionWith
  :: forall {c} (x :: c) w s a wo o
   . (CopyDiscard c, Ob x, Ob w, Ob s, Ob a, Ob wo, Ob o)
  => AttentionSteps x w s a wo o -> w ** w ** w ** wo ** x ~> o
attentionWith st = toSMC @(F w :** F w :** F w :** F wo :** F x) \(wq, wk, wv, wo, x) ->
  let q = lift @(F x :** F w) @(F s) (project st) (x ** wq)
      k = lift @(F x :** F w) @(F s) (project st) (x ** wk)
      v = lift @(F x :** F w) @(F s) (project st) (x ** wv)
      a = lift @(F s :** F s) @(F a) (weigh st) (q ** k)
  in lift @(F s :** F wo) @(F o) (output st) (lift @(F a :** F s) @(F s) (mix st) (a ** v) ** wo)

-- | Attention on sequences of four positions with two features each, and a number for each
-- position: queries, keys and values of dimension 4, the scores scaled by @1/2@ and their softmax for
-- each query.
attention :: Para (DF '[8, 8, 8, 4]) (DF '[8]) (DF '[4])
attention =
  Reader
    ( attentionWith @(DF '[8]) @(DF '[8]) @(DF '[16]) @(DF '[16]) @(DF '[4]) @(DF '[4])
        AttentionSteps
          { project = matMat @4 @2 @4
          , weigh =
              softmax @4 @4 . pointwise (/ 2) (const 0.5) . bilinear @'[4, 4] @'[4, 4] (scores @(TN '[4]) @(TN '[4]) @(TN '[4]))
          , mix = matMat @4 @4 @4
          , output = matMat @4 @4 @1
          }
    )

-- | Attention drawn with a box for each step, and a wire for each matrix: the sequence, the
-- weights, the queries, keys and values, the attention weights and the result.
attentionPicture :: String
attentionPicture =
  render
    ( attentionWith @(S '[Wire "X"]) @(S '[Wire "W"]) @(S '[Wire "H"]) @(S '[Wire "A"]) @(S '[Wire "Wₒ"]) @(S '[Wire "Y"])
        AttentionSteps
          { project = node "X·W"
          , weigh = node "softmax(Q·Kᵀ/√d)"
          , mix = node "A·V"
          , output = node "H·Wₒ"
          }
    )

-- | Attention drawn with a wire for each index: positions @i@, features @f@, the dimension @k@ of
-- queries and keys, and the output @o@, with the weighing opened up into the wiring of 'scores'.
attentionWiringPicture :: String
attentionWiringPicture =
  render
    ( attentionWith @(S '[Wire "i", Wire "f"]) @(S '[Wire "f", Wire "k"]) @(S '[Wire "i", Wire "k"])
        @(S '[Wire "i", Wire "i"])
        @(S '[Wire "k", Wire "o"])
        @(S '[Wire "i", Wire "o"])
        AttentionSteps
          { project = node "·W"
          , weigh =
              node @'[Wire "i", Wire "i"] "softmax"
                . node @'[Wire "i", Wire "i"] "/√d"
                . scores @(S '[Wire "i"]) @(S '[Wire "i"]) @(S '[Wire "k"])
          , mix = node "A·V"
          , output = node "·Wₒ"
          }
    )

-- | Sequences of four values between -1 and 1, spread around an offset of their own, each value
-- with the constant 1 as its second feature, and as target the largest value at every position.
sequences :: [Int] -> [Point '[8, 4]]
sequences ns =
  [ Point [SV.fromList (concat [[x, 1] | x <- xs]), SV.replicate 4 (maximum xs)]
  | n <- ns
  , let xs = [0.5 * sin (fromIntegral (7 * n + 3 * j) * 1.3) + 0.4 * sin (fromIntegral n * 2.1) | j <- [0 .. 3 :: Int]]
  ]

-- | Small weights of both signs.
attentionStart :: Point '[8, 8, 8, 4]
attentionStart = fromCoordinates (SV.generate (sum (dimsOf @'[8, 8, 8, 4])) \i -> 0.5 * sin (fromIntegral (i * i + 3)))

-- | The average distance between the prediction and the largest value, over all positions.
maxError :: Point '[8, 8, 8, 4] -> [Point '[8, 4]] -> Double
maxError w samples = sum errors / fromIntegral (length errors)
  where
    errors =
      [ abs (p - t)
      | (x, Vector ts) <- map (split @'[8] @'[4]) samples
      , (p, t) <- zip (SV.toList (coordinates (predict attention w x))) (SV.toList ts)
      ]

test :: TestTree
test =
  testGroup
    "Learning"
    [ testProperty "linear regression recovers the coefficients" do
        let w =
              coordinates (train (gradientDescent 0.02) 50 (loss squaredError (affine @9)) zero (batches @3 @1 @9 regressionSamples))
        check
          ("found " ++ show (SV.toList w))
          (SV.and (SV.zipWith (\a b -> abs (a - b) < 1e-3) w (SV.fromList [1, -2, 0.5, 0.3])))
    , testProperty "a perceptron learns exclusive or in batches of two" do
        learnsXor (train (gradientDescent 0.2) 200 (loss squaredError (perceptron @2)) xorStart (batches @2 @1 @2 xorSamples))
    , testProperty "from one batch, momentum learns in fifty passes, where plain gradient descent at the same rate stalls" do
        let still = xorLoss (train (gradientDescent 0.05) 50 (loss squaredError (perceptron @4)) xorStart xorBatch)
        check ("loss " ++ show still) (still > 0.01)
        learnsXor (snd (train (momentum 0.05 0.9) 50 (loss squaredError (perceptron @4)) (zero, xorStart) xorBatch))
    , testProperty "a classifier tells three rings apart, also on points it has not seen" do
        let w =
              snd
                ( train
                    (momentum 0.01 0.9)
                    100
                    (loss (softmaxCrossEntropy @3 @16) (classifier @16))
                    (zero, classifierStart)
                    (batches @2 @3 @16 (rings [0 .. 95]))
                )
            seen = accuracy w (rings [0 .. 95])
            unseen = accuracy w (rings [96 .. 191])
        check ("accuracy " ++ show seen) (seen == 1)
        check ("accuracy on unseen points " ++ show unseen) (unseen >= 0.95)
    , testProperty "attention learns to find the largest value, also in sequences it has not seen" do
        let w = snd (train (momentum 0.01 0.9) 200 (loss squaredError attention) (zero, attentionStart) (sequences [0 .. 63]))
            seen = maxError w (sequences [0 .. 63])
            unseen = maxError w (sequences [64 .. 127])
        check ("error " ++ show seen) (seen < 0.03)
        check ("error on unseen sequences " ++ show unseen) (unseen < 0.03)
    , testProperty "attention draws, with a box for each step and with the weighing as wiring" do
        check
          "not an SVG document"
          (and ["<svg" `isInfixOf` p | p <- [attentionPicture, attentionWiringPicture]])
    ]

-- | The loss of the perceptron with the given parameters on exclusive or.
xorLoss :: Point '[4, 2, 2, 1] -> Double
xorLoss w = sum [SV.head (coordinates (predict (loss squaredError (perceptron @4)) w s)) | s <- xorBatch]

-- | The perceptron with the given parameters has a small loss and gets every case right.
learnsXor :: Point '[4, 2, 2, 1] -> Property ()
learnsXor w = do
  let l = xorLoss w
      predictions = [(predict (perceptron @4) w inputs, targets) | (inputs, targets) <- map (split @'[4 * 2] @'[4]) xorBatch]
  check ("loss " ++ show l) (l < 0.01)
  check
    ("predicted " ++ show [SV.toList p | (Vector p, _) <- predictions])
    (and [SV.and (SV.zipWith (\q t -> signum q == t) p y) | (Vector p, Vector y) <- predictions])
