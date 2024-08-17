{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Proarrow.Profunctor.Forget where

import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromMaybe)
import Data.Semigroup (Semigroup (..))
import Prelude (Maybe (..), Monoid (..), foldMap, ($))

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Core (CategoryOf (..), OB, PRO, Profunctor (..), Promonad (..))
import Proarrow.Functor (Functor (..))
import Proarrow.Object (Ob')
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Object.Terminal (El)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type Forget :: forall (ob :: OB k) -> PRO k (SUBCAT ob)
data Forget ob a b where
  Forget :: (ob b) => a ~> b -> Forget ob a (SUB b)

instance (CategoryOf k) => Profunctor (Forget (ob :: OB k)) where
  dimap l (Sub r) (Forget f) = Forget (r . f . l)
  r \\ Forget f = r \\ f

instance (CategoryOf k) => Representable (Forget (ob :: OB k)) where
  type Forget ob % (SUB a) = a
  index (Forget f) = f
  tabulate = Forget
  repMap (Sub f) = f

type List :: PRO (SUBCAT Monoid) Type
data List a b where
  List :: (Monoid a) => (a -> [b]) -> List (SUB a) b
instance Profunctor List where
  dimap = dimapRep
  r \\ List{} = r

instance Representable List where
  type List % a = SUB [a]
  index (List f) = Sub f
  tabulate (Sub f) = List f
  repMap f = Sub (map f)

instance Adjunction List (Forget Monoid) where
  unit = Forget (: []) :.: List id
  counit (List g :.: Forget f) = Sub (foldMap f . g)

type HasFree :: forall {k}. (k -> Constraint) -> Constraint
class (forall a. (Super c a) => c (Free c a), Functor (Free c)) => HasFree (c :: k -> Constraint) where
  type Super c :: k -> Constraint
  type Super c = Ob'
  type Free c :: k -> k
  lift :: (Super c a) => a ~> Free c a
  retract :: (c a) => Free c a ~> a

instance HasFree Semigroup where
  type Free Semigroup = NonEmpty
  lift = (:| [])
  retract = sconcat

instance HasFree Monoid where
  type Super Monoid = Semigroup
  type Free Monoid = Maybe
  lift = Just
  retract = fromMaybe mempty

type Ap :: (k -> Type) -> k -> Type
data Ap f a where
  Pure :: El a -> Ap f a
  Eff :: f a -> Ap f a
  LiftA2 :: (Ob a, Ob b) => (a && b ~> c) -> Ap f a -> Ap f b -> Ap f c

instance (CategoryOf k, Functor f) => Functor (Ap (f :: k -> Type)) where
  map f (Pure a) = Pure (f . a)
  map f (Eff x) = Eff (map f x)
  map f (LiftA2 k x y) = LiftA2 (f . k) x y

instance Functor Ap where
  map (Nat n) = Nat $ \case
    Pure a -> Pure a
    Eff fa -> Eff (n fa)
    LiftA2 k x y -> LiftA2 k (unNat (map (Nat n)) x) (unNat (map (Nat n)) y)

instance (HasProducts k, Functor f) => Applicative (Ap (f :: k -> Type)) where
  pure a () = Pure a
  liftA2 f (fa, fb) = LiftA2 f fa fb

retractAp :: (Applicative f) => Ap f a -> f a
retractAp (Pure a) = pure a ()
retractAp (Eff fa) = fa
retractAp (LiftA2 k x y) = liftA2 k (retractAp x, retractAp y)

instance (HasProducts k) => HasFree (Applicative :: (k -> Type) -> Constraint) where
  type Free Applicative = Ap
  lift = Nat Eff
  retract = Nat retractAp
