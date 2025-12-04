{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Profunctor.Free where

import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (Maybe (..), fromMaybe)
import Data.Semigroup (Semigroup (..))
import Prelude (($))
import Prelude qualified as P

import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..), TracedMonoidal', toInt)
import Proarrow.Category.Instance.Nat (Nat (..), first)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (On, SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), swap)
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..), (==), (||))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , OB
  , Profunctor (..)
  , Promonad (..)
  , UN
  , arr
  , lmap
  , obj
  , rmap
  , src
  , (//)
  , type (+->)
  )
import Proarrow.Functor (Functor (..), FunctorForRep (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Dual (CompactClosed, Dual, dualObj, dualityCounit, dualityUnit)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.List (LIST (..), List (..))
import Proarrow.Profunctor.Representable (Representable (..), trivialRep)
import Proarrow.Profunctor.Star (Star, pattern Star)

type HasFree :: forall {k}. (k -> Constraint) -> Constraint
class (CategoryOf k, Representable (Free ob), forall b. (Ob b) => ob (Free ob % b)) => HasFree (ob :: k -> Constraint) where
  type Free ob :: k +-> k
  lift' :: a ~> b -> Free ob a b
  retract' :: (ob b) => Free ob a b -> a ~> b

lift :: forall ob a. (HasFree ob, Ob a) => a ~> Free ob % a
lift = index @(Free ob) (lift' @ob id)

retract :: forall ob a. (HasFree ob, ob a, Ob a) => Free ob % a ~> a
retract = retract' @ob trivialRep

fold :: forall ob a b. (HasFree ob, ob b) => (a ~> b) -> Free ob % a ~> b
fold f = retract' @ob (rmap f trivialRep) \\ f

data family FreeSub :: forall (ob :: OB k) -> k +-> SUBCAT ob
instance (HasFree ob) => FunctorForRep (FreeSub ob) where
  type FreeSub ob @ a = SUB (Free ob % a)
  fmap f = Sub (repMap @(Free ob) f) \\ f
-- | By creating the right adjoint to the free functor,
-- we obtain the free-forgetful adjunction.
instance (HasFree ob) => Representable (Corep (FreeSub (ob :: OB k))) where
  type Corep (FreeSub ob) % a = UN SUB a
  index (Corep (Sub f)) = f . lift @ob
  tabulate f = Corep (Sub (retract @ob . repMap @(Free ob) f)) \\ f
  repMap (Sub f) = f

instance HasFree P.Monoid where
  type Free P.Monoid = Star []
  lift' f = Star ((: []) . f)
  retract' (Star f) = P.mconcat . f

instance HasFree Semigroup where
  type Free Semigroup = Star NonEmpty
  lift' f = Star ((:| []) . f)
  retract' (Star f) = sconcat . f

instance HasFree (P.Monoid `On` Semigroup) where
  type Free (P.Monoid `On` Semigroup) = Sub (Star Maybe) :: CAT (SUBCAT Semigroup)
  lift' (Sub f) = Sub (Star (Just . f))
  retract' (Sub (Star f)) = Sub (fromMaybe P.mempty . f)

type Ap :: (k -> Type) -> k -> Type
data Ap f a where
  Pure :: Unit ~> a -> Ap f a
  Eff :: f a -> Ap f a
  LiftA2 :: (Ob a, Ob b) => (a ** b ~> c) -> Ap f a -> Ap f b -> Ap f c

instance (CategoryOf k, Functor f) => Functor (Ap (f :: k -> Type)) where
  map f (Pure a) = Pure (f . a)
  map f (Eff x) = Eff (map f x)
  map f (LiftA2 k x y) = LiftA2 (f . k) x y

instance Functor Ap where
  map (Nat n) = Nat $ \case
    Pure a -> Pure a
    Eff fa -> Eff (n fa)
    LiftA2 k x y -> LiftA2 k (first (Nat n) x) (first (Nat n) y)

instance (Monoidal k, Functor f) => Applicative (Ap (f :: k -> Type)) where
  pure a () = Pure a
  liftA2 f (fa, fb) = LiftA2 f fa fb

instance (Monoidal k, Monoid m) => Monoid (Ap (f :: k -> Type) m) where
  mempty () = Pure mempty
  mappend (l, r) = LiftA2 mappend l r

retractAp :: (Applicative f) => Ap f a -> f a
retractAp (Pure a) = pure a ()
retractAp (Eff fa) = fa
retractAp (LiftA2 k x y) = liftA2 k (retractAp x, retractAp y)

instance (Monoidal k) => HasFree (Applicative :: (k -> Type) -> Constraint) where
  type Free Applicative = Star Ap
  lift' (Nat f) = Star (Nat (Eff . f))
  retract' (Star (Nat f)) = Nat (retractAp . f)

data FreePromonad p a b where
  Unit :: (a ~> b) -> FreePromonad p a b
  Comp :: p b c -> FreePromonad p a b -> FreePromonad p a c

instance (Profunctor p) => Profunctor (FreePromonad p) where
  dimap l r (Unit f) = Unit (r . f . l)
  dimap l r (Comp p q) = Comp (rmap r p) (lmap l q)
  r \\ (Unit f) = r \\ f
  r \\ Comp p q = r \\ p \\ q

instance (Profunctor p) => Promonad (FreePromonad p) where
  id = Unit id
  Unit f . q = rmap f q
  Comp r p . q = Comp r (p . q)
instance Functor FreePromonad where
  map n =
    n // Prof \case
      Unit g -> Unit g
      Comp p q -> Comp (unProf n p) (unProf (map n) q)
instance HasFree Promonad where
  type Free Promonad = Star FreePromonad
  lift' (Prof f) = Star (Prof \a -> f a `Comp` Unit (src a))
  retract' (Star (Prof n)) = Prof \p -> case n p of
    Unit f -> arr f
    Comp q r -> q . unProf (retract @Promonad) r

class
  (forall k. (b k) => c (f k)) =>
  HasFreeK (b :: Kind -> Constraint) (c :: Kind -> Constraint) (f :: Kind -> Kind)
    | b c -> f
  where
  type Lift b c f (a :: k) :: f k
  type Retract b c f (a :: f k) :: k
  liftK :: (b k) => (x :: k) ~> y -> Lift b c f x ~> Lift b c f y
  retractK :: (c k) => (x :: f k) ~> y -> Retract b c f x ~> Retract b c f y

instance HasFreeK CategoryOf Monoidal LIST where
  type Lift CategoryOf Monoidal LIST a = L '[a]
  type Retract CategoryOf Monoidal LIST (a :: LIST k) = Fold (UN L a)
  liftK f = Cons f Nil
  retractK Nil = par0
  retractK (Cons f Nil) = f
  retractK (Cons f fs@Cons{}) = f `par` retractK @CategoryOf @Monoidal fs

instance HasFreeK TracedMonoidal' CompactClosed INT where
  type Lift TracedMonoidal' CompactClosed INT (a :: k) = I a Unit
  type Retract TracedMonoidal' CompactClosed INT (I a b :: INT k) = a ** Dual b
  liftK = toInt
  retractK (Int @ap @am @bp @bm f) =
    dualObj @am //
      dualObj @bm //
        unStr $
          Str @[ap, Dual am] @[Dual am, ap] (swap @_ @ap @(Dual am)) || Str @'[] @[bm, Dual bm] (dualityUnit @bm)
            == obj @'[Dual am] || Str @[ap, bm] @[am, bp] f || obj @'[Dual bm]
            == Str @[Dual am, am] @'[] (dualityCounit @am) || obj @'[bp] || obj @'[Dual bm]