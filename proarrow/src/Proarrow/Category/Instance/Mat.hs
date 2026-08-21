{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Mat where

import Data.Complex (Complex, conjugate)
import Data.Kind (Type)
import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat, snatToNat, type Mult, type Plus)
import Data.Vec.Lazy (Vec (..), chunks, concat, concatMap, reifyList, tabulate, toList, zipWith, (++))
import Prelude (($), type (~))
import Prelude qualified as P

import Data.Fin (Fin)
import Proarrow.Adjunction (Involution)
import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.FinSet (FINSET (..), FinSet (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..), coactCC)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Distributive (Distributive (..), distLInv, distRInv)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, Hypergraph)
import Proarrow.Category.Monoidal.StarAutonomous (ExpSA, StarAutonomous (..), applySA, currySA, expSA)
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), defaultFactorize)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasBiproducts)
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..), pushoutDefault)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..), pullbackDefault)
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Rep (..))

type n + m = Plus n m
type (*) n m = Mult n m

type data MatK (a :: Type) = M Nat

data Mat :: CAT (MatK a) where
  Mat
    :: forall {a} m n
     . (IsNat m, IsNat n)
    => {unMat :: Vec n (Vec m a)}
    -> Mat (M m :: MatK a) (M n)

app :: (P.Num a, P.Applicative (Vec m)) => Vec n (Vec m a) -> Vec m a -> Vec n a
app m v = P.fmap (P.sum . P.liftA2 (P.*) v) m

arr :: forall n m a. (P.Num a) => FinSet (FS m) (FS n) -> Mat (M n :: MatK a) (M m :: MatK a)
arr (FinSet v) = withIsNat @n $ withIsNat @m $ Mat (P.fmap oneV v)

arr' :: forall n m a. (P.Num a) => FinSet (FS m) (FS n) -> Mat (M m :: MatK a) (M n :: MatK a)
arr' (FinSet v) = withIsNat @n $ withIsNat @m $ Mat (P.traverse oneV v)

oneV :: (P.Num a, IsNat n) => Fin n -> Vec n a
oneV m = tabulate \n -> if n P.== m then 1 else 0

zero :: (P.Num a, IsNat n) => Vec n a
zero = P.pure 0

withIsNat :: forall n r. (SNatI n) => ((IsNat n) => r) -> r
withIsNat r = case snat @n of
  SZ -> r
  SS @n' -> withIsNat @n' r

class (SNatI n, P.Applicative (Vec n), n + Z ~ n, n * Z ~ Z, n * S Z ~ n) => IsNat (n :: Nat) where
  matId :: (P.Num a) => Vec n (Vec n a)
  withPlusNat :: (IsNat m) => ((IsNat (n + m)) => r) -> r
  withMultNat :: (IsNat m) => ((IsNat (n * m)) => r) -> r
  withPlusSucc :: (IsNat m) => ((n + (S m) ~ S (n + m)) => r) -> r
  withMultSucc :: (IsNat m) => ((n * (S m) ~ n + (n * m)) => r) -> r
  withPlusSym :: (IsNat m) => (((n + m) ~ (m + n)) => r) -> r
  withMultSym :: (IsNat m) => (((n * m) ~ (m * n)) => r) -> r
  withAssocPlus :: (IsNat m, IsNat o) => (((n + m) + o ~ n + (m + o)) => r) -> r
  withAssocMult :: (IsNat m, IsNat o) => (((n * m) * o ~ n * (m * o)) => r) -> r
  withDist :: (IsNat m, IsNat o) => (((n + m) * o ~ (n * o) + (m * o)) => r) -> r
instance IsNat Z where
  matId = VNil
  withPlusNat r = r
  withMultNat r = r
  withPlusSucc r = r
  withMultSucc r = r
  withPlusSym r = r
  withMultSym r = r
  withAssocPlus r = r
  withAssocMult r = r
  withDist r = r
instance (IsNat n) => IsNat (S n) where
  matId = (1 ::: zero) ::: P.fmap (0 :::) matId
  withPlusNat @m r = withPlusNat @n @m r
  withMultNat @m r = withMultNat @n @m (withPlusNat @m @(n * m) r)
  withPlusSucc @m r = withPlusSucc @n @m r
  withMultSucc @m r =
    withMultNat @n @m $
      withAssocPlus @n @m @(n * m) $
        withPlusSym @n @m $
          withAssocPlus @m @n @(n * m) $
            withMultSucc @n @m r
  withPlusSym @m r = withPlusSucc @m @n $ withPlusSym @n @m r
  withMultSym @m r = withMultSucc @m @n $ withMultSym @n @m r
  withAssocPlus @m @o r = withAssocPlus @n @m @o r
  withAssocMult @m @o r = withMultNat @n @m $ withAssocMult @n @m @o (withDist @m @(n * m) @o r)
  withDist @m @o r = withMultNat @n @o $ withMultNat @m @o $ withAssocPlus @o @(n * o) @(m * o) $ withDist @n @m @o r

instance {-# OVERLAPPABLE #-} (P.Num a) => DaggerProfunctor (Mat :: CAT (MatK a)) where
  dagger (Mat m) = Mat (P.sequenceA m)

instance {-# OVERLAPS #-} (P.RealFloat a) => DaggerProfunctor (Mat :: CAT (MatK (Complex a))) where
  dagger (Mat m) = Mat (P.traverse (P.fmap conjugate) m)

instance (P.Num a) => Profunctor (Mat :: CAT (MatK a)) where
  dimap = dimapDefault
  r \\ Mat{} = r
instance (P.Num a) => Promonad (Mat :: CAT (MatK a)) where
  id = Mat matId
  Mat m . n = case dagger n of Mat nT -> Mat (P.fmap (app nT) m)

-- | The category of matrices with entries in a type @a@, where the objects are natural numbers and the arrows @n ~> m@ are matrices of dimension @n@ by @m@.
instance (P.Num a) => CategoryOf (MatK a) where
  type (~>) = Mat
  type Ob n = (Is M n, IsNat (UN M n))

instance (P.Num a) => HasInitialObject (MatK a) where
  type InitialObject = M Z
  initiate = Mat (P.pure VNil)
instance (P.Num a) => HasTerminalObject (MatK a) where
  type TerminalObject = M Z
  terminate = Mat VNil

instance (P.Num a) => HasBinaryCoproducts (MatK a) where
  type M x || M y = M (x + y)
  withObCoprod @(M x) @(M y) r = withPlusNat @x @y r
  lft @(M m) @(M n) = withPlusNat @m @n (Mat (matId @m ++ (zero P.<$ matId @n @a)))
  rgt @(M m) @(M n) = withPlusNat @m @n (Mat ((zero P.<$ matId @m @a) ++ matId @n))
  Mat @m a ||| Mat @n b = withPlusNat @m @n (Mat (P.liftA2 (++) a b))
instance (P.Num a) => HasBinaryProducts (MatK a) where
  type M x && M y = M (x + y)
  withObProd @(M x) @(M y) r = withPlusNat @x @y r
  fst @(M m) @(M n) = withPlusNat @m @n (Mat (P.fmap (++ (0 P.<$ matId @n @a)) (matId @m)))
  snd @(M m) @(M n) = withPlusNat @m @n (Mat (P.fmap ((0 P.<$ matId @m @a) ++) (matId @n)))
  Mat @_ @m a &&& Mat @_ @n b = withPlusNat @m @n (Mat (a ++ b))
instance (P.Num a) => HasBiproducts (MatK a)

-- | The equalizer of two linear maps @f, g :: M m ~> M n@ is the kernel of @f - g@: the subspace of
-- @M m@ on which they agree. Computed by row-reducing @f - g@ to reduced row echelon form; the free
-- (non-pivot) columns of the result index a basis of the kernel.
--
-- >>> import Data.Vec.Lazy (Vec(..))
-- >>> let f = Mat @(S (S Z)) @(S Z) ((1 ::: 2 ::: VNil) ::: VNil) :: Mat (M (S (S Z))) (M (S Z) :: MatK P.Double)
-- >>> let g = Mat @(S (S Z)) @(S Z) ((3 ::: 0 ::: VNil) ::: VNil) :: Mat (M (S (S Z))) (M (S Z) :: MatK P.Double)
-- >>> let h = Mat @(S Z) @(S (S Z)) ((1 ::: VNil) ::: (1 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S (S Z)) :: MatK P.Double)
-- >>> (equalize f g \incl@(Mat inclv) -> case factorEqualizer incl h of p@(Mat pv) -> P.show (inclv, pv, unMat (incl . p))) :: P.String
-- "((1.0 ::: VNil) ::: (1.0 ::: VNil) ::: VNil,(1.0 ::: VNil) ::: VNil,(1.0 ::: VNil) ::: (1.0 ::: VNil) ::: VNil)"
instance (P.Fractional a, P.Eq a) => HasEqualizers (MatK a) where
  equalize (Mat @m @_ l) (Mat r) cont =
    let
      diffRows = toList (zipWith (zipWith (P.-)) l r) :: [Vec m a]
      numCols = P.fromIntegral (snatToNat (snat @m)) :: P.Int
      (pivotCols, finalRows) = rref numCols diffRows
      pivotMap = P.zip pivotCols finalRows
      freeCols = P.filter (`P.notElem` pivotCols) [0 .. numCols P.- 1]
      basisFor :: P.Int -> Vec m a
      basisFor j' = tabulate entryAt
        where
          entryAt fi =
            let i = P.fromEnum fi
            in if i P.== j'
                 then 1
                 else
                   if i `P.elem` freeCols
                     then 0
                     else P.maybe 0 (P.negate . (`at` j')) (P.lookup i pivotMap)
    in
      reifyList (P.map basisFor freeCols) \(vecs :: Vec e (Vec m a)) ->
        withIsNat @e $ cont (Mat (P.sequenceA vecs) :: Mat (M e :: MatK a) (M m))

  -- @incl@ need not literally be the RREF-derived basis 'equalize' produces; any mono @incl@ works,
  -- since we row-reduce the columns of @incl@ and @h@ concatenated (bounding pivot search to just
  -- @incl@'s width): full column rank turns @incl@'s part into an identity submatrix for free, and
  -- Gaussian elimination carries the same row operations through @h@'s columns alongside it.
  factorEqualizer (Mat @e @_ incl) (Mat @e' j) =
    let
      numColsE = P.fromIntegral (snatToNat (snat @e)) :: P.Int
      combinedRows = P.zipWith (++) (toList incl) (toList j)
      (_, finalRows) = rref numColsE combinedRows
      hRow fi =
        let rest = P.drop numColsE (toList (finalRows P.!! P.fromEnum fi))
        in tabulate (\fj -> rest P.!! P.fromEnum fj) :: Vec e' a
    in
      Mat (tabulate hRow)

-- | The coequalizer of @f, g :: M m ~> M n@ is the cokernel of @f - g@, i.e. the quotient of @M n@ by
-- its image. Rather than a separate algorithm, this reuses the equalizer machinery via @dagger@: since
-- @dagger@ is a contravariant involution on 'Mat', a coequalizer of @f, g@ is exactly an equalizer of
-- @dagger f, dagger g@ transported back across @dagger@.
--
-- >>> let f = Mat @(S Z) @(S (S Z)) ((2 ::: VNil) ::: (0 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S (S Z)) :: MatK P.Double)
-- >>> let g = Mat @(S Z) @(S (S Z)) ((0 ::: VNil) ::: (3 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S (S Z)) :: MatK P.Double)
-- >>> let w = Mat @(S (S Z)) @(S Z) ((3 ::: 2 ::: VNil) ::: VNil) :: Mat (M (S (S Z))) (M (S Z) :: MatK P.Double)
-- >>> (coequalize f g \q@(Mat qv) -> case factorCoequalizer q w of s@(Mat sv) -> P.show (qv, sv, unMat (s . q))) :: P.String
-- "((1.5 ::: 1.0 ::: VNil) ::: VNil,(2.0 ::: VNil) ::: VNil,(3.0 ::: 2.0 ::: VNil) ::: VNil)"
instance (P.Fractional a, P.Eq a) => HasCoequalizers (MatK a) where
  coequalize f g cont = equalize (dagger f) (dagger g) \incl -> cont (dagger incl)
  factorCoequalizer q h = dagger (factorEqualizer (dagger q) (dagger h))

-- | Pullbacks are computed via 'pullbackDefault', as the equalizer of @f . fst@ and @g . snd@ on the
-- product @a && b@ -- the standard linear-algebra construction of a fiber product of vector spaces.
--
-- >>> let f = Mat @(S Z) @(S Z) ((2 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S Z) :: MatK P.Double)
-- >>> let g = Mat @(S Z) @(S Z) ((3 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S Z) :: MatK P.Double)
-- >>> (pullback f g \p q -> case (p, q) of (Mat pv, Mat qv) -> P.show (pv, qv)) :: P.String
-- "((1.5 ::: VNil) ::: VNil,(1.0 ::: VNil) ::: VNil)"
instance (P.Fractional a, P.Eq a) => HasPullbacks (MatK a) where
  pullback = pullbackDefault

-- | Pushouts are computed via 'pushoutDefault', as the coequalizer of @lft . f@ and @rgt . g@ on the
-- coproduct @a || b@ -- the standard linear-algebra construction of a cofiber product of vector spaces.
--
-- >>> let f = Mat @(S Z) @(S Z) ((2 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S Z) :: MatK P.Double)
-- >>> let g = Mat @(S Z) @(S Z) ((3 ::: VNil) ::: VNil) :: Mat (M (S Z)) (M (S Z) :: MatK P.Double)
-- >>> (pushout f g \p q -> case (p, q) of (Mat pv, Mat qv) -> P.show (pv, qv)) :: P.String
-- "((1.5 ::: VNil) ::: VNil,(1.0 ::: VNil) ::: VNil)"
instance (P.Fractional a, P.Eq a) => HasPushouts (MatK a) where
  pushout = pushoutDefault

-- | Epi-mono factorization is computed via 'defaultFactorize': @f@ factors as the coequalizer of its
-- cokernel pair (the epi onto its image) followed by the equalizer factorization of @f@ through that
-- epi (the mono inclusion of the image).
--
-- >>> let h = Mat @(S (S Z)) @(S (S Z)) ((1 ::: 2 ::: VNil) ::: (2 ::: 4 ::: VNil) ::: VNil) :: Mat (M (S (S Z))) (M (S (S Z)) :: MatK P.Double)
-- >>> (case factorize h of e :.: m -> case (e, m) of (Mat ev, Mat mv) -> P.show (ev, mv, unMat (m . e))) :: P.String
-- "((2.0 ::: 4.0 ::: VNil) ::: VNil,(0.5 ::: VNil) ::: (1.0 ::: VNil) ::: VNil,(1.0 ::: 2.0 ::: VNil) ::: (2.0 ::: 4.0 ::: VNil) ::: VNil)"
instance (P.Fractional a, P.Eq a) => HasEpiMonoFactorization (MatK a) where
  factorize :: forall (x :: MatK a) y. (x ~> y) -> (Mat :.: Mat) x y
  factorize = defaultFactorize

-- | Reads the entry of a row at a runtime column index.
at :: Vec m a -> P.Int -> a
at v i = toList v P.!! i

-- | Row-reduces the given matrix, given as a list of rows of the given width, to reduced row echelon
-- form, returning the ascending pivot column indices together with the reduced rows.
rref :: (P.Fractional a, P.Eq a) => P.Int -> [Vec m a] -> ([P.Int], [Vec m a])
rref numCols rows0 = go 0 0 rows0
  where
    numRows = P.length rows0
    go rowPtr col rows
      | col P.>= numCols P.|| rowPtr P.>= numRows = ([], rows)
      | P.otherwise =
          let (before, atOrAfter) = P.splitAt rowPtr rows
          in case P.break (\row -> row `at` col P./= 0) atOrAfter of
               (_, []) -> go rowPtr (col P.+ 1) rows
               (skipped, pivotRow : rest) ->
                 let
                   normalized = P.fmap (P./ (pivotRow `at` col)) pivotRow
                   eliminate row =
                     let f = row `at` col
                     in if f P.== 0 then row else zipWith (\x y -> x P.- f P.* y) row normalized
                   rows' = P.map eliminate before P.++ (normalized : P.map eliminate (skipped P.++ rest))
                 in
                   case go (rowPtr P.+ 1) (col P.+ 1) rows' of
                     (pivots, final) -> (col : pivots, final)

instance (P.Num a) => MonoidalProfunctor (Mat :: CAT (MatK a)) where
  one = id
  Mat @fx @fy f ** Mat @gx @gy g =
    withMultNat @gx @fx $
      withMultNat @gy @fy $
        Mat $
          concatMap (\grow -> P.fmap (\frow -> concatMap (\a -> P.fmap (a P.*) frow) grow) f) g

-- | Products of the dimensions of the matrices as the tensor. This is the Kronecker product of matrices.
instance (P.Num a) => Monoidal (MatK a) where
  type Unit = M (S Z)
  type M x ** M y = M (y * x)
  withOb2 @(M x) @(M y) r = withMultNat @y @x r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) ** (obj @(M c) ** obj @(M d)))
  associatorInv @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) ** (obj @(M c) ** obj @(M d)))

instance (P.Num a) => SymMonoidal (MatK a) where
  swap @(M x) @(M y) = arr (swap @_ @(FS x) @(FS y))

instance (P.Num a) => Distributive (MatK a) where
  distL @(M a') @(M b) @(M c) = arr (distRInv @(FS b) @(FS c) @(FS a'))
  distR @(M a') @(M b) @(M c) = arr (distLInv @(FS c) @(FS a') @(FS b))
  absorbL = id
  absorbR = id

instance (P.Num a) => Closed (MatK a) where
  type x ~~> y = ExpSA x y
  withObExp @(M x) @(M y) r = withMultNat @y @x r
  curry @x @y = currySA @x @y
  apply @y @z = applySA @y @z
  (^^^) = expSA

instance (P.Num a) => StarAutonomous (MatK a) where
  type Dual n = n
  withObDual r = r
  dual = dagger
  dualInv = dagger
  linDist @(M x) @(M y) @(M z) (Mat m) = withMultNat @z @y $ Mat (concat (P.fmap (chunks @y @x) m))
  linDistInv @(M x) @(M y) @(M z) (Mat m) = withMultNat @y @x $ Mat (P.fmap concat (chunks @z @y m))

instance (P.Num a) => CompactClosed (MatK a) where
  distribDual @m @n = withMultNat @(UN M m) @(UN M n) $ dagger (obj @m) ** dagger (obj @n)
  dualUnit = id

instance (P.Num a, MonoidalAction (t :: (MatK a, MatK a) +-> MatK a)) => Costrong t (Mat :: CAT (MatK a)) where
  coact @x = coactCC @t @x

-- | Monoids are associative, unital algebras.
instance (P.Num a, IsNat n) => Monoid (M n :: MatK a) where
  mempty = arr counit
  mappend = arr comult

instance (P.Num a, IsNat n) => Comonoid (M n :: MatK a) where
  counit = arr' counit
  comult = arr' comult
instance (P.Num a, IsNat n) => Frobenius (M n :: MatK a)
instance (P.Num a) => Hypergraph (MatK a)
instance (P.Num a) => CopyDiscard (MatK a)

data family Conjugate :: MatK (Complex a) +-> MatK (Complex a)
instance (P.RealFloat a) => FunctorForRep (Conjugate :: MatK (Complex a) +-> MatK (Complex a)) where
  type Conjugate @ n = n
  fmap (Mat m) = Mat (P.fmap (P.fmap conjugate) m)

-- | Conjugation is a self-adjoint functor
instance (P.RealFloat a) => Corepresentable (Rep Conjugate :: MatK (Complex a) +-> MatK (Complex a)) where
  type Rep Conjugate %% n = n
  coindex (Rep f) = f
  cotabulate f = Rep f \\ f
  corepMap = fmap @Conjugate

instance (P.RealFloat a) => Involution (Rep Conjugate :: MatK (Complex a) +-> MatK (Complex a))
instance (P.RealFloat a) => MonoidalProfunctor (Rep Conjugate :: MatK (Complex a) +-> MatK (Complex a)) where
  one = Rep one
  Rep l ** Rep r = let lr = l ** r in Rep lr \\ lr

data family App :: MatK a +-> Type
instance (P.Num a) => FunctorForRep (App :: MatK a +-> Type) where
  type App @a @ M n = Vec n a
  fmap (Mat m) = app m
instance (P.Num a) => MonoidalProfunctor (Rep App :: MatK a +-> Type) where
  one = Rep \() -> 1 ::: VNil
  Rep @b f ** Rep @c g = withOb2 @_ @b @c $ Rep (\(x, y) -> concatMap (\a -> (a P.*) P.<$> f x) (g y))
