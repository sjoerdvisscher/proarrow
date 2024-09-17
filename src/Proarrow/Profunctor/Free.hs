{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Proarrow.Profunctor.Free where

import Data.Kind (Constraint)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (Maybe (..), fromMaybe)
import Data.Monoid (Monoid (..))
import Data.Semigroup (Semigroup (..))

import Proarrow.Adjunction (Adjunction (..), counitFromRepCounit, unitFromRepUnit)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (On, SUBCAT (..), Sub (..), SubP (..))
import Proarrow.Core (CategoryOf (..), Kind, OB, Profunctor (..), Promonad (..), arr, lmap, rmap, src, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Forget (Forget)
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, repObj)
import Proarrow.Profunctor.Star (Star (..))

type HasFree :: forall {k}. (k -> Constraint) -> Constraint
class (CategoryOf k, Representable (Free ob), forall b. (Ob b) => ob (Free ob % b)) => HasFree (ob :: k -> Constraint) where
  type Free ob :: k +-> k
  lift' :: a ~> b -> Free ob a b
  retract' :: (ob b) => Free ob a b -> a ~> b

lift :: forall ob a. (HasFree ob, Ob a) => a ~> Free ob % a
lift = index @(Free ob) (lift' @ob id)

retract :: forall ob a. (HasFree ob, ob a, Ob a) => Free ob % a ~> a
retract = retract' @ob (tabulate @(Free ob) (repObj @(Free ob) @a))

type FreeSub :: forall (ob :: OB k) -> k +-> SUBCAT ob
data FreeSub ob a b where
  FreeSub :: (ob a) => Free ob a b -> FreeSub ob (SUB a) b

instance (HasFree ob) => Profunctor (FreeSub ob) where
  dimap = dimapRep
  r \\ FreeSub p = r \\ p

instance (HasFree ob) => Representable (FreeSub ob) where
  type FreeSub ob % a = SUB (Free ob % a)
  index (FreeSub p) = Sub (index p) \\ p
  tabulate (Sub f) = FreeSub (tabulate f)
  repMap f = Sub (repMap @(Free ob) f) \\ f

instance (HasFree ob) => Adjunction (FreeSub ob) (Forget ob) where
  unit = unitFromRepUnit (lift @ob)
  counit = counitFromRepCounit (Sub (retract @ob))

instance HasFree Monoid where
  type Free Monoid = Star []
  lift' f = Star ((: []) . f)
  retract' (Star f) = mconcat . f

instance HasFree Semigroup where
  type Free Semigroup = Star NonEmpty
  lift' f = Star ((:| []) . f)
  retract' (Star f) = sconcat . f

instance HasFree (Monoid `On` Semigroup) where
  type Free (Monoid `On` Semigroup) = SubP Semigroup (Star Maybe)
  lift' (Sub f) = SubP (Star (Just . f))
  retract' (SubP (Star f)) = Sub (fromMaybe mempty . f)

-- type Ap :: (k -> Type) -> k -> Type
-- data Ap f a where
--   Pure :: El a -> Ap f a
--   Eff :: f a -> Ap f a
--   LiftA2 :: (Ob a, Ob b) => (a && b ~> c) -> Ap f a -> Ap f b -> Ap f c

-- instance (CategoryOf k, Functor f) => Functor (Ap (f :: k -> Type)) where
--   map f (Pure a) = Pure (f . a)
--   map f (Eff x) = Eff (map f x)
--   map f (LiftA2 k x y) = LiftA2 (f . k) x y

-- instance Functor Ap where
--   map (Nat n) = Nat $ \case
--     Pure a -> Pure a
--     Eff fa -> Eff (n fa)
--     LiftA2 k x y -> LiftA2 k (unNat (map (Nat n)) x) (unNat (map (Nat n)) y)

-- instance (HasProducts k, Functor f) => Applicative (Ap (f :: k -> Type)) where
--   pure a () = Pure a
--   liftA2 f (fa, fb) = LiftA2 f fa fb

-- retractAp :: (Applicative f) => Ap f a -> f a
-- retractAp (Pure a) = pure a ()
-- retractAp (Eff fa) = fa
-- retractAp (LiftA2 k x y) = liftA2 k (retractAp x, retractAp y)

-- instance (HasProducts k) => HasFree (Joker (Applicative :: (k -> Type) -> Constraint)) where
--   type Free (Joker Applicative) = Star Ap
--   lift (Nat f) = Star (Nat (Eff . f))
--   lower (Star (Nat f)) = Nat (retractAp . f)

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

class (Ob (Lift c f a)) => ObLift c f k (a :: k)
instance (Ob (Lift c f a)) => ObLift c f k a
class (Ob (Retract c f a)) => ObRetract c f k (a :: f k)
instance (Ob (Retract c f a)) => ObRetract c f k (a :: f k)
class (forall a. ObLift c f k a, forall a. ObRetract c f k a) => ObLiftRetract c f k
instance (forall a. ObLift c f k a, forall a. ObRetract c f k a) => ObLiftRetract c f k

class
  (forall k. (CategoryOf k) => c (f k), forall k. ObLiftRetract c f k) =>
  HasFreeK (c :: Kind -> Constraint) (f :: Kind -> Kind)
    | c -> f
  where
  type Lift c f (a :: k) :: f k
  type Retract c f (a :: f k) :: k
  liftK :: (CategoryOf k) => (a :: k) ~> b -> Lift c f a ~> Lift c f b
  retractK :: (c k) => (a :: f k) ~> b -> Retract c f a ~> Retract c f b

-- instance HasFreeK Monoidal [] where
--   type Lift Monoidal [] a = '[a]
--   type Retract Monoidal [] a = Fold a
--   liftK = singleton
--   retractK (Str f) = f