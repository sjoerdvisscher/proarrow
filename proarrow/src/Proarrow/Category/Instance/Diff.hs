{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | __Differentiable maps__ between products of real vector spaces, with their reverse derivatives.
-- An object is a list of dimensions, @'DF' '[n, m]@ for ℝⁿ × ℝᵐ, and an arrow is a map together
-- with its reverse derivative: given a point and a change of the output, the change of the input
-- it comes from. Running an arrow at a point gives the image together with the reverse derivative
-- there, so the backward pass reuses what the forward pass computed, as in Elliott's
-- /The simple essence of automatic differentiation/. Composition runs the maps forward and chains
-- the reverse derivatives backward, which is the chain rule, so a reverse derivative is never more
-- than a change of vectors passed back through each step.
--
-- The category is cartesian: copying a point is adding the changes that come back, and discarding
-- one is the zero change. Every object is a commutative monoid by adding vectors. 'toLens' gives
-- an arrow as a lens, with the map as the view and the reverse derivative as the update.
--
-- The reverse derivative is a function rather than an arrow of the category itself, so this is the
-- first-order part of a reverse derivative category: the derivative cannot be differentiated again.
module Proarrow.Category.Instance.Diff
  ( DIFF (..)
  , Diff (..)
  , forward
  , backward
  , diff
  , Point (..)
  , pattern Vector
  , coordinates
  , fromCoordinates
  , zero
  , add
  , scale
  , split
  , append
  , linear
  , pointwise
  , times
  , dot
  , matVec
  , matMat
  , broadcast
  , softmax
  , softmaxCrossEntropy
  , bilinear
  , constant
  , toLens
  , Forget
  , AsLens
  ) where

import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Vector.Storable qualified as SV
import GHC.TypeNats (KnownNat, Nat, natVal, type (*))
import Prelude (Double, ($), (*), (+))
import Prelude qualified as P

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.TensorNetwork (Size, TNET (..), dimsOf, fromVector, matMul, toVector)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Category.Monoidal.Hypergraph (cap)
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..))
import Proarrow.Object (KnownListOf (..), withKnownAppend, withKnownAssoc, type (++))
import Proarrow.Optic (OPTIC (..), Prostrong)
import Proarrow.Optic.Lens (Lens, LensFl, lens)

-- | Objects are lists of dimensions, the product of the spaces of those dimensions.
type data DIFF = DF [Nat]

-- | A point of a product of spaces, or a change of one: a vector of coordinates for each space.
-- Taking a point of a product apart and putting it together handles the vectors without copying
-- their coordinates.
type Point :: [Nat] -> Type
newtype Point ns = Point {vectors :: [SV.Vector Double]}

-- | A point of a single space.
pattern Vector :: SV.Vector Double -> Point '[n]
pattern Vector v = Point [v]

{-# COMPLETE Vector #-}

-- | The dimension of a space.
dim :: forall n. (KnownNat n) => P.Int
dim = P.fromIntegral (natVal (Proxy @n))

-- | The coordinates of a point, one space after the other.
coordinates :: Point ns -> SV.Vector Double
coordinates (Point vs) = SV.concat vs

-- | The point with the given coordinates, one space after the other.
fromCoordinates :: forall ns. (KnownListOf KnownNat ns) => SV.Vector Double -> Point ns
fromCoordinates = Point P.. go (dimsOf @ns)
  where
    go [] _ = []
    go (d : ds) v = let (l, r) = SV.splitAt d v in l : go ds r

-- | The origin, which is also the change that changes nothing.
{-# INLINE zero #-}
zero :: forall ns. (KnownListOf KnownNat ns) => Point ns
zero = Point (P.map (`SV.replicate` 0) (dimsOf @ns))

-- | The sum of two points, or two changes.
{-# INLINE add #-}
add :: Point ns -> Point ns -> Point ns
add (Point x) (Point y) = Point (P.zipWith (SV.zipWith (+)) x y)

-- | A point, or a change, multiplied by a number.
{-# INLINE scale #-}
scale :: Double -> Point ns -> Point ns
scale s (Point x) = Point (P.map (SV.map (s *)) x)

-- | A point of a product as its two parts.
{-# INLINE split #-}
split :: forall as bs. (KnownListOf KnownNat as) => Point (as ++ bs) -> (Point as, Point bs)
split = \(Point vs) -> let (l, r) = P.splitAt n vs in (Point l, Point r)
  where
    n = P.length (dimsOf @as)

-- | The point of a product with the given parts.
{-# INLINE append #-}
append :: Point as -> Point bs -> Point (as ++ bs)
append (Point l) (Point r) = Point (l P.++ r)

-- | A differentiable map: at a point, its image and its reverse derivative there, which takes a
-- change of the image to the change of the point it comes from.
type Diff :: CAT DIFF
data Diff a b where
  Diff
    :: forall as bs
     . (KnownListOf KnownNat as, KnownListOf KnownNat bs)
    => {run :: Point as -> (Point bs, Point bs -> Point as)}
    -> Diff (DF as) (DF bs)

-- | The map of an arrow.
{-# INLINE forward #-}
forward :: DF as ~> DF bs -> Point as -> Point bs
forward f x = P.fst (run f x)

-- | The reverse derivative of an arrow at a point.
{-# INLINE backward #-}
backward :: DF as ~> DF bs -> Point as -> Point bs -> Point as
backward f x = P.snd (run f x)

-- | The arrow with the given map and reverse derivative, for when the two share no work.
{-# INLINE diff #-}
diff
  :: (KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => (Point as -> Point bs) -> (Point as -> Point bs -> Point as) -> DF as ~> DF bs
diff f fb = Diff (\x -> (f x, fb x))

-- | The identity between two lists of spaces that are the same list.
same :: forall as bs. (KnownListOf KnownNat as, KnownListOf KnownNat bs) => DF as ~> DF bs
same = Diff (\x -> (coerce x, coerce))

instance Profunctor Diff where
  dimap = dimapDefault
  r \\ Diff{} = r

instance Promonad Diff where
  id = same
  Diff g . Diff f = Diff \x -> let (y, fb) = f x; (z, gb) = g y in (z, fb P.. gb)

-- | Differentiable maps between products of real vector spaces.
instance CategoryOf DIFF where
  type (~>) = Diff
  type Ob a = (Is DF a, KnownListOf KnownNat (UN DF a))

instance MonoidalProfunctor Diff where
  one = id
  Diff @as @bs f ** Diff @cs @ds g =
    withKnownAppend @KnownNat @as @cs $
      withKnownAppend @KnownNat @bs @ds $
        Diff \x ->
          let (a, c) = split @as @cs x; (b, fb) = f a; (d, gb) = g c
          in (append b d, \dy -> let (db, dd) = split @bs @ds dy in append (fb db) (gb dd))

-- | The product of spaces as the tensor.
instance Monoidal DIFF where
  type Unit = DF '[]
  type a ** b = DF (UN DF a ++ UN DF b)
  withOb2 @a @b r = withObProd @DIFF @a @b r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor @(DF as) = withKnownAppend @KnownNat @as @'[] same
  rightUnitorInv @(DF as) = withKnownAppend @KnownNat @as @'[] same
  associator @(DF as) @(DF bs) @(DF cs) = withKnownAssoc @KnownNat @as @bs @cs same
  associatorInv @(DF as) @(DF bs) @(DF cs) = withKnownAssoc @KnownNat @as @bs @cs same

instance SymMonoidal DIFF where
  swap @(DF as) @(DF bs) =
    withKnownAppend @KnownNat @as @bs $
      withKnownAppend @KnownNat @bs @as $
        diff
          (\x -> let (a, b) = split @as @bs x in append b a)
          (\_ d -> let (db, da) = split @bs @as d in append da db)

-- | The one-point space.
instance HasTerminalObject DIFF where
  type TerminalObject = DF '[]
  terminate = constant zero

-- | The product of spaces: the reverse derivative of a pairing adds the changes of both parts.
instance HasBinaryProducts DIFF where
  type a && b = DF (UN DF a ++ UN DF b)
  withObProd @(DF as) @(DF bs) r = withKnownAppend @KnownNat @as @bs r
  fst @(DF as) @(DF bs) = withKnownAppend @KnownNat @as @bs $ diff (P.fst P.. split @as @bs) (\_ da -> append da (zero @bs))
  snd @(DF as) @(DF bs) = withKnownAppend @KnownNat @as @bs $ diff (P.snd P.. split @as @bs) (\_ db -> append (zero @as) db)
  Diff @_ @bs f &&& Diff @_ @cs g =
    withKnownAppend @KnownNat @bs @cs $
      Diff \x ->
        let (b, fb) = f x; (c, gb) = g x
        in (append b c, \d -> let (db, dc) = split @bs @cs d in add (fb db) (gb dc))

-- | Copying a point: the changes that come back are added.
instance (KnownListOf KnownNat ns) => Comonoid (DF ns :: DIFF) where
  counit = terminate
  comult = id &&& id

instance (KnownListOf KnownNat ns) => CocommutativeComonoid (DF ns :: DIFF)
instance CopyDiscard DIFF

-- | Adding vectors: the change of a sum is passed back to both terms.
instance (KnownListOf KnownNat ns) => Monoid (DF ns :: DIFF) where
  mempty = constant zero
  mappend = withKnownAppend @KnownNat @ns @ns $ diff (\x -> let (a, b) = split @ns @ns x in add a b) (\_ d -> append d d)

instance (KnownListOf KnownNat ns) => CommutativeMonoid (DF ns :: DIFF)

-- | A linear map, given as a tensor network, its input and result each the vector of a tensor's
-- entries. The change of the input is the change of the result through the 'dual' of the map.
linear
  :: forall as bs
   . (KnownListOf KnownNat as, KnownListOf KnownNat bs, KnownNat (Size as), KnownNat (Size bs))
  => (TN as :: TNET Double) ~> TN bs
  -> DF '[Size as] ~> DF '[Size bs]
linear f =
  diff
    (\(Vector x) -> Vector (toVector (f . fromVector @'[] x)))
    (\_ (Vector dz) -> Vector (toVector (dual f . fromVector @'[] dz)))

-- | A function applied to each coordinate, given with its derivative.
pointwise :: (KnownNat n) => (Double -> Double) -> (Double -> Double) -> DF '[n] ~> DF '[n]
pointwise f f' = diff (\(Vector x) -> Vector (SV.map f x)) (\(Vector x) (Vector d) -> Vector (SV.zipWith (*) (SV.map f' x) d))

-- | The coordinatewise product of two vectors: 'bilinear' with the merging spider, written out.
times :: forall n. (KnownNat n) => DF '[n, n] ~> DF '[n]
times = Diff \p ->
  let (Vector x, Vector y) = split @'[n] @'[n] p
  in (Vector (SV.zipWith (*) x y), \(Vector d) -> Point [SV.zipWith (*) d y, SV.zipWith (*) d x])

-- | The dot product of two vectors: 'bilinear' with the cap, which sums the products.
dot :: forall n. (KnownNat n) => DF '[n, n] ~> DF '[1]
dot = bilinear @'[n] @'[n] (cap @(TN '[n]))

-- | The product of an @m@ by @n@ matrix, given row by row, with a vector: 'matMat' with a single
-- column.
matVec :: forall m n. (KnownNat m, KnownNat n, KnownNat (m * n)) => DF '[m * n, n] ~> DF '[m]
matVec = matMat @m @n @1

-- | The product of an @m@ by @n@ matrix with an @n@ by @k@ matrix, both given row by row. With a
-- batch of @m@ vectors as the rows of the first, the second is a linear map applied to each of them.
-- It is 'bilinear' with the cap on the summed index, written out with 'matMul': the change of the
-- first matrix is the change of the result times the transposed second, and the change of the second
-- is the transposed first times the change of the result, which adds up the changes from the whole
-- batch.
matMat
  :: forall m n k
   . (KnownNat m, KnownNat n, KnownNat k, KnownNat (m * n), KnownNat (n * k), KnownNat (m * k))
  => DF '[m * n, n * k] ~> DF '[m * k]
matMat = Diff \p ->
  let (Vector x, Vector w) = split @'[m * n] @'[n * k] p
  in ( Vector (matMul P.False P.False m k n x w)
     , \(Vector dy) -> Point [matMul P.False P.True m n k dy w, matMul P.True P.False n k m x dy]
     )
  where
    m = dim @m
    n = dim @n
    k = dim @k

-- | A vector copied to each of the @b@ rows of a matrix, given row by row: for adding the same
-- vector to each of a batch of @b@ vectors. The change of the vector adds up the rows of the change
-- of the matrix.
broadcast :: forall m b. (KnownNat m, KnownNat b, KnownNat (b * m)) => DF '[m] ~> DF '[b * m]
broadcast =
  diff
    (\(Vector v) -> Vector (SV.concat (P.replicate b v)))
    (\_ (Vector d) -> Vector (P.foldl' (SV.zipWith (+)) (SV.replicate m 0) (rows b m d)))
  where
    m = dim @m
    b = dim @b

-- | The softmax of each of the @b@ rows of a matrix of scores, given row by row: the exponentials of
-- a row divided by their sum, for each of a batch of @b@ vectors a probability for each of @k@
-- classes. The change of a row of scores is the probabilities times the change of the row minus its
-- average under them.
softmax :: forall k b. (KnownNat k, KnownNat b, KnownNat (b * k)) => DF '[b * k] ~> DF '[b * k]
softmax = Diff \(Vector z) ->
  let ps = P.map (SV.map P.exp P.. logSoftmax) (rows b k z)
  in ( Vector (SV.concat ps)
     , \(Vector d) ->
         Vector
           ( SV.concat
               ( P.zipWith
                   (\p dr -> let average = SV.sum (SV.zipWith (*) dr p) in SV.zipWith (\q e -> q * (e P.- average)) p dr)
                   ps
                   (rows b k d)
               )
           )
     )
  where
    k = dim @k
    b = dim @b

-- | The cross-entropy of the softmax of each of the @b@ rows of a matrix of scores against the same
-- row of a matrix of target probabilities, both given row by row, summed over the rows: the loss of
-- a classifier on a batch. With the softmax computed along, the change of the scores is the
-- probabilities minus the targets, for targets that sum to 1, and the change of the targets is
-- minus the logarithms of the probabilities.
softmaxCrossEntropy :: forall k b. (KnownNat k, KnownNat b, KnownNat (b * k)) => DF '[b * k, b * k] ~> DF '[1]
softmaxCrossEntropy = Diff \x ->
  let (Vector z, Vector t) = split @'[b * k] @'[b * k] x
      logPs = P.map logSoftmax (rows b k z)
      logP = SV.concat logPs
  in ( Vector (SV.singleton (P.negate (SV.sum (SV.zipWith (*) t logP))))
     , \(Vector d) ->
         let s = SV.head d
             scores lp tr = let mass = SV.sum tr in SV.zipWith (\l e -> s * (P.exp l * mass P.- e)) lp tr
         in Point [SV.concat (P.zipWith scores logPs (rows b k t)), SV.map (\l -> P.negate (s * l)) logP]
     )
  where
    k = dim @k
    b = dim @b

-- | A bilinear map, given as a tensor network from the tensor product of its two inputs, each input
-- and the result the vector of a tensor's entries: 'linear' in each input. The change of one input
-- is the change of the result through the 'dual' of the map with the other input fixed.
bilinear
  :: forall as bs cs
   . ( KnownListOf KnownNat as
     , KnownListOf KnownNat bs
     , KnownListOf KnownNat cs
     , KnownNat (Size as)
     , KnownNat (Size bs)
     , KnownNat (Size cs)
     )
  => (TN (as ++ bs) :: TNET Double) ~> TN cs
  -> DF '[Size as, Size bs] ~> DF '[Size cs]
bilinear f = withKnownAppend @KnownNat @as @bs $ Diff \p ->
  let (Vector x, Vector y) = split @'[Size as] @'[Size bs] p
      tx = fromVector @'[] @as x
      ty = fromVector @'[] @bs y
      withY = f . (obj @(TN as) ** ty) . rightUnitorInv @_ @(TN as)
      withX = f . (tx ** obj @(TN bs))
  in ( Vector (toVector (f . (tx ** ty)))
     , \(Vector dz) ->
         let tdz = fromVector @'[] dz
         in Point [toVector (dual withY . tdz), toVector (dual withX . tdz)]
     )

-- | The logarithms of the softmax of a vector, with its largest entry taken out before the
-- exponentials so that they cannot overflow.
logSoftmax :: SV.Vector Double -> SV.Vector Double
logSoftmax z = SV.map (P.subtract logSum) z
  where
    m = SV.maximum z
    logSum = m + P.log (SV.sum (SV.map (\x -> P.exp (x P.- m)) z))

-- | The @b@ rows of length @k@ of a matrix given row by row.
rows :: P.Int -> P.Int -> SV.Vector Double -> [SV.Vector Double]
rows b k v = [SV.slice (j * k) k v | j <- P.enumFromTo 0 (b P.- 1)]

-- | The map to a fixed point, whose reverse derivative is the zero change.
constant :: forall as bs. (KnownListOf KnownNat as, KnownListOf KnownNat bs) => Point bs -> DF as ~> DF bs
constant p = Diff (P.const (p, P.const zero))

-- | An arrow as a lens: the map is the view, and the reverse derivative the update. Composing
-- arrows and composing their lenses agree, which is the chain rule; 'AsLens' is the functor. A lens
-- views and updates separately, so the update runs the map again.
toLens :: DF as ~> DF bs -> Lens (Point as) (Point as) (Point bs) (Point bs)
toLens f = lens (forward f) (P.uncurry (backward f))

-- | The underlying functions: a differentiable map as a function from the points of its source to
-- those of its target, forgetting the reverse derivative.
data family Forget :: DIFF +-> Type

instance FunctorForRep Forget where
  type Forget @ a = Point (UN DF a)
  fmap f@Diff{} = forward f

-- | Arrows as lenses, by 'toLens'. The lens of an arrow goes the other way, so this is a functor into
-- the opposite of the category of lenses, and that it is a functor is the chain rule.
data family AsLens :: DIFF +-> OPPOSITE (OPTIC Type Type (Prostrong LensFl))

instance FunctorForRep AsLens where
  type AsLens @ a = OP (OPT (Point (UN DF a)) (Point (UN DF a)))
  fmap f@Diff{} = Op (toLens f)
