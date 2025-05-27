{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Mat where

import Data.Complex (Complex, conjugate)
import Data.Kind (Type)
import Prelude (($), type (~))
import Prelude qualified as P

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (Costrong (..), MonoidalAction (..), Strong (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj)
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Dual
  ( CompactClosed (..)
  , ExpSA
  , StarAutonomous (..)
  , compactClosedCoact
  , currySA
  , expSA
  , uncurrySA
  )
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))

type data Nat = Z | S Nat

type family (+) (a :: Nat) (b :: Nat) :: Nat where
  Z + b = b
  S a + b = S (a + b)
type family (*) (a :: Nat) (b :: Nat) :: Nat where
  Z * b = Z
  S a * b = b + (a * b)

data Vec :: Nat -> Type -> Type where
  Nil :: Vec Z a
  Cons :: a -> Vec n a -> Vec (S n) a

instance P.Functor (Vec n) where
  fmap _ Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (P.fmap f xs)
instance P.Foldable (Vec n) where
  foldMap _ Nil = P.mempty
  foldMap f (Cons x xs) = f x P.<> P.foldMap f xs
instance P.Traversable (Vec n) where
  traverse _ Nil = P.pure Nil
  traverse f (Cons x xs) = Cons P.<$> f x P.<*> P.traverse f xs

instance P.Applicative (Vec Z) where
  pure _ = Nil
  Nil <*> Nil = Nil
instance (P.Applicative (Vec n)) => P.Applicative (Vec (S n)) where
  pure x = Cons x (P.pure x)
  Cons f fs <*> Cons x xs = Cons (f x) (fs P.<*> xs)

type data MatK (a :: Type) = M Nat
type instance UN M (M n) = n

data Mat :: CAT (MatK a) where
  Mat
    :: forall {a} {m'} {n'} m n
     . (Ob m', Ob n', m' ~ (M m :: MatK a), n' ~ M n)
    => Vec n (Vec m a)
    -> Mat m' n'

apply :: (P.Num a, P.Applicative (Vec m)) => Vec n (Vec m a) -> Vec m a -> Vec n a
apply m v = P.fmap (P.sum . P.liftA2 (P.*) v) m

class (P.Applicative (Vec n), n + Z ~ n, n * Z ~ Z, n * S Z ~ n) => IsNat (n :: Nat) where
  matId :: (P.Num a) => Vec n (Vec n a)
  zero :: (P.Num a) => Vec n a
  append :: Vec n a -> Vec m a -> Vec (n + m) a
  split :: Vec (n + m) a -> (Vec n a, Vec m a)
  concatMap :: (IsNat m) => (a -> Vec m b) -> Vec n a -> Vec (n * m) b
  unConcatMap :: (IsNat m) => (Vec m b -> a) -> Vec (n * m) b -> Vec n a
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
  matId = Nil
  zero = Nil
  append Nil ys = ys
  split ys = (Nil, ys)
  concatMap _ Nil = Nil
  unConcatMap _ Nil = Nil
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
  matId = Cons (Cons 1 zero) (P.fmap (Cons 0) matId)
  zero = Cons 0 zero
  append (Cons x xs) ys = Cons x (append xs ys)
  split (Cons x xs) = case split xs of (ys, zs) -> (Cons x ys, zs)
  concatMap f (Cons x xs) = f x `append` concatMap f xs
  unConcatMap f mnm = case split mnm of (m, nm) -> f m `Cons` unConcatMap f nm
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

withNat :: Vec n a -> ((IsNat n) => r) -> r
withNat Nil r = r
withNat (Cons _ xs) r = withNat xs r

mat :: (Ob (M m)) => Vec n (Vec m a) -> Mat (M m :: MatK a) (M n)
mat m = withNat m (Mat m)

instance {-# OVERLAPPABLE #-} (P.Num a) => DaggerProfunctor (Mat :: CAT (MatK a)) where
  dagger (Mat m) = Mat (P.sequenceA m)

instance {-# OVERLAPS #-} (P.RealFloat a) => DaggerProfunctor (Mat :: CAT (MatK (Complex a))) where
  dagger (Mat m) = Mat (P.fmap (P.fmap conjugate) (P.sequenceA m))

instance (P.Num a) => Profunctor (Mat :: CAT (MatK a)) where
  dimap = dimapDefault
  r \\ Mat{} = r
instance (P.Num a) => Promonad (Mat :: CAT (MatK a)) where
  id = Mat matId
  Mat m . n = case dagger n of Mat nT -> Mat (P.fmap (apply nT) m)
instance (P.Num a) => CategoryOf (MatK a) where
  type (~>) = Mat
  type Ob n = (Is M n, IsNat (UN M n))

instance (P.Num a) => HasInitialObject (MatK a) where
  type InitialObject = M Z
  initiate = Mat (P.pure Nil)
instance (P.Num a) => HasTerminalObject (MatK a) where
  type TerminalObject = M Z
  terminate = Mat Nil

instance (P.Num a) => HasBinaryCoproducts (MatK a) where
  type M x || M y = M (x + y)
  withObCoprod @(M x) @(M y) r = withPlusNat @x @y r
  lft @(M m) @(M n) = mat (append (matId @m) (zero P.<$ matId @n @a))
  rgt @(M m) @(M n) = mat (append (zero P.<$ matId @m @a) (matId @n))
  Mat @m a ||| Mat @n b = withPlusNat @m @n (Mat (P.liftA2 append a b))
instance (P.Num a) => HasBinaryProducts (MatK a) where
  type M x && M y = M (x + y)
  withObProd @(M x) @(M y) r = withPlusNat @x @y r
  fst @(M m) @(M n) = withPlusNat @m @n (Mat (P.fmap (`append` (0 P.<$ matId @n @a)) (matId @m)))
  snd @(M m) @(M n) = withPlusNat @m @n (Mat (P.fmap (append (0 P.<$ matId @m @a)) (matId @n)))
  Mat a &&& Mat b = mat (append a b)

instance (P.Num a) => MonoidalProfunctor (Mat :: CAT (MatK a)) where
  par0 = id
  Mat @fx @fy f `par` Mat @gx @gy g =
    withMultNat @gx @fx $
      withMultNat @gy @fy $
        Mat $
          concatMap (\grow -> P.fmap (\frow -> concatMap (\a -> P.fmap (a P.*) frow) grow) f) g

instance (P.Num a) => Monoidal (MatK a) where
  type Unit = M (S Z)
  type M x ** M y = M (y * x)
  withOb2 @(M x) @(M y) = withMultNat @y @x
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) `par` (obj @(M c) `par` obj @(M d)))
  associatorInv @(M b) @(M c) @(M d) = withAssocMult @d @c @b (obj @(M b) `par` (obj @(M c) `par` obj @(M d)))

instance (P.Num a) => SymMonoidal (MatK a) where -- TODO: test this
  swap @(M x) @(M y) =
    withMultNat @x @y $
      withMultNat @y @x $
        Mat $
          concatMap @x @y (\x -> P.fmap (\b -> concatMap @y @x (\a -> P.fmap (a P.*) x) b) (matId @y @a)) (matId @x @a)

instance (P.Num a) => Closed (MatK a) where
  type x ~~> y = ExpSA x y
  withObExp @(M x) @(M y) r = withMultNat @y @x r
  curry @x @y = currySA @x @y
  uncurry @y @z = uncurrySA @_ @y @z
  (^^^) = expSA

instance (P.Num a) => StarAutonomous (MatK a) where
  type Dual n = n
  dual = dagger
  dualInv = dagger
  linDist @(M x) @(M y) @(M z) (Mat m) = withMultNat @z @y $ Mat (concatMap id (P.fmap (unConcatMap @y @x id) m))
  linDistInv @(M x) @(M y) @(M z) (Mat m) = withMultNat @y @x $ Mat (P.fmap (concatMap id) (unConcatMap @z @y id m))

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

instance (P.Num a) => Strong (MatK a) (Mat :: CAT (MatK a)) where
  act = par

instance (P.Num a) => Costrong (MatK a) (Mat :: CAT (MatK a)) where
  coact @x = compactClosedCoact @x