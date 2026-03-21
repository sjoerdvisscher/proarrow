{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Mat where

import Data.Complex (Complex, conjugate)
import Data.Kind (Type)
import Data.Type.Nat (Nat (..), SNatI, type Mult, type Plus)
import Data.Vec.Lazy (Vec (..), chunks, concat, concatMap, tabulate, (++))
import Prelude (($), type (~))
import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (Costrong (..), MonoidalAction (..), Strong (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
import Proarrow.Monoid (Comonoid (..), CopyDiscard, Monoid (..))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), HasBiproducts)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Dual
  ( CompactClosed (..)
  , ExpSA
  , StarAutonomous (..)
  , applySA
  , compactClosedCoact
  , currySA
  , expSA
  )
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Identity (Id (..))

type n + m = Plus n m
type (*) n m = Mult n m

type data MatK (a :: Type) = M Nat
type instance UN M (M n) = n

data Mat :: CAT (MatK a) where
  Mat
    :: forall {a} {m'} {n'} m n
     . (Ob m', Ob n', m' ~ (M m :: MatK a), n' ~ M n)
    => Vec n (Vec m a)
    -> Mat m' n'

app :: (P.Num a, P.Applicative (Vec m)) => Vec n (Vec m a) -> Vec m a -> Vec n a
app m v = P.fmap (P.sum . P.liftA2 (P.*) v) m

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
  matId = (1 ::: zero) ::: (P.fmap (0 :::) matId)
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

zero :: (P.Num a, IsNat n) => Vec n a
zero = P.pure 0

withNat :: Vec n a -> ((IsNat n) => r) -> r
withNat VNil r = r
withNat (_ ::: xs) r = withNat xs r

mat :: (IsNat m) => Vec n (Vec m a) -> Mat (M m :: MatK a) (M n)
mat m = withNat m (Mat m)

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
  lft @(M m) @(M n) = mat (matId @m ++ (zero P.<$ matId @n @a))
  rgt @(M m) @(M n) = mat ((zero P.<$ matId @m @a) ++ matId @n)
  Mat @m a ||| Mat @n b = withPlusNat @m @n (Mat (P.liftA2 (++) a b))
instance (P.Num a) => HasBinaryProducts (MatK a) where
  type M x && M y = M (x + y)
  withObProd @(M x) @(M y) r = withPlusNat @x @y r
  fst @(M m) @(M n) = withPlusNat @m @n (Mat (P.fmap (++ (0 P.<$ matId @n @a)) (matId @m)))
  snd @(M m) @(M n) = withPlusNat @m @n (Mat (P.fmap ((0 P.<$ matId @m @a) ++) (matId @n)))
  Mat a &&& Mat b = mat (a ++ b)
instance (P.Num a) => HasBiproducts (MatK a)

instance (P.Num a) => MonoidalProfunctor (Mat :: CAT (MatK a)) where
  par0 = id
  Mat @fx @fy f `par` Mat @gx @gy g =
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
  associator @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) `par` (obj @(M c) `par` obj @(M d)))
  associatorInv @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) `par` (obj @(M c) `par` obj @(M d)))

instance (P.Num a) => SymMonoidal (MatK a) where
  swap @(M x) @(M y) =
    withMultNat @x @y $
      withMultNat @y @x $
        Mat $
          concatMap @_ @y @_ @x
            (\x -> P.fmap (\b -> concatMap @_ @x @_ @y (\a -> P.fmap (a P.*) x) b) (matId @y @a))
            (matId @x @a)

instance (P.Num a) => Closed (MatK a) where
  type x ~~> y = ExpSA x y
  withObExp @(M x) @(M y) r = withMultNat @y @x r
  curry @x @y = currySA @x @y
  apply @y @z = applySA @y @z
  (^^^) = expSA

instance (P.Num a) => StarAutonomous (MatK a) where
  type Dual n = n
  dual = dagger
  dualInv = dagger
  linDist @(M x) @(M y) @(M z) (Mat m) = withMultNat @z @y $ Mat (concat (P.fmap (chunks @y @x) m))
  linDistInv @(M x) @(M y) @(M z) (Mat m) = withMultNat @y @x $ Mat (P.fmap concat (chunks @z @y m))

instance (P.Num a) => CompactClosed (MatK a) where
  distribDual @m @n = withMultNat @(UN M m) @(UN M n) $ dagger (obj @m) `par` dagger (obj @n)
  dualUnit = id

instance (P.Num a) => MonoidalAction (MatK a) (MatK a) where
  type Act p x = p ** x
  withObAct @b @c r = withOb2 @_ @b @c r
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) `par` (obj @(M c) `par` obj @(M d)))
  multiplicatorInv @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) `par` (obj @(M c) `par` obj @(M d)))

instance (P.Num a) => Strong (MatK a) (Id :: CAT (MatK a)) where
  act = par . Id

instance (P.Num a) => Costrong (MatK a) (Mat :: CAT (MatK a)) where
  coact @x = compactClosedCoact @x

instance (P.Num a, IsNat n) => Monoid (M n :: MatK a) where
  mempty = Mat $ P.pure $ P.pure 1
  mappend = withMultNat @n @n $ Mat $
    tabulate \i -> concat $
      tabulate \j ->
        tabulate \k -> if i P.== j P.&& j P.== k then 1 else 0
instance (P.Num a, IsNat n) => Comonoid (M n :: MatK a) where
  counit = Mat $ P.pure $ P.pure 1
  comult = withMultNat @n @n $
    Mat $
      concat $
        tabulate \i ->
          tabulate \j ->
            tabulate \k ->
              if i P.== j P.&& j P.== k then 1 else 0
instance (P.Num a) => CopyDiscard (MatK a)

-- Monoids are associative, unital algebras.