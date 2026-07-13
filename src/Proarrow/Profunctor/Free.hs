{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Free where

import Data.Foldable1 (Foldable1 (foldMap1))
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (Maybe (..))
import Prelude (($))
import Prelude qualified as P

import Proarrow.Category.Instance.IntConstruction (INT (..), IntConstruction (..), toInt)
import Proarrow.Category.Instance.Nat (Nat (..), first)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (Forget, On, SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), swap)
import Proarrow.Category.Monoidal.Action (TracedMonoidal)
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
  , tgt
  , (//)
  , (:~>)
  )
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (Monoid (..))
import Proarrow.Object.Dual (CompactClosed, Dual, dualObj, dualityCounit, dualityUnit)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.List (LIST (..), List (..))
import Proarrow.Profunctor.Representable (Rep (..))
import Proarrow.Profunctor.Star (Star, pattern Star)

type HasFree :: forall {k}. OB k -> Constraint
class (CategoryOf k, forall a. (Ob a) => ob (Free ob a)) => HasFree (ob :: OB k) where
  type Free ob (a :: k) :: k
  lift :: (Ob a) => a ~> Free ob a
  foldMap :: (ob b) => (a ~> b) -> Free ob a ~> b

retract :: forall ob a. (HasFree ob, ob a, Ob a) => Free ob a ~> a
retract = foldMap @ob id

freeMap :: (HasFree ob) => (a ~> b) -> Free ob a ~> Free ob b
freeMap @ob f = foldMap @ob (lift @ob . f) \\ f

freeComp :: (HasFree ob, Ob c) => b ~> Free ob c -> a ~> Free ob b -> a ~> Free ob c
freeComp @ob l r = foldMap @ob l . r

-- | By creating the left adjoint to the forgetful functor,
-- we obtain the free-forgetful adjunction.
instance (HasFree ob) => Corepresentable (Rep (Forget (ob :: OB k))) where
  type Rep (Forget ob) %% a = SUB (Free ob a)
  coindex (Rep f) = Sub (foldMap @ob f) \\ f
  corepUniv @a = let f = lift @ob @a in Rep f \\ f

instance HasFree P.Monoid where
  type Free P.Monoid a = [a]
  lift = P.pure
  foldMap = P.foldMap

instance HasFree P.Semigroup where
  type Free P.Semigroup a = NonEmpty a
  lift = P.pure
  foldMap = foldMap1

instance HasFree (P.Monoid `On` P.Semigroup) where
  type Free (P.Monoid `On` P.Semigroup) (SUB a) = SUB (Maybe a)
  lift = Sub Just
  foldMap (Sub f) = Sub (P.foldMap f)

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

instance (Monoidal k) => Promonad (Star Ap :: CAT (k -> Type)) where
  id = Star (lift @Applicative)
  Star l . Star r = Star (freeComp @Applicative l r)

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

instance (Monoidal k) => HasFree (Applicative :: OB (k -> Type)) where
  type Free Applicative f = Ap f
  lift = Nat Eff
  foldMap f@Nat{} = Nat retractAp . map f

data FreePromonad p a b where
  Unit :: (a ~> b) -> FreePromonad p a b
  Comp :: p a b -> FreePromonad p b c -> FreePromonad p a c

freePromonadAlg :: p :.: FreePromonad p :~> FreePromonad p
freePromonadAlg (p :.: pp) = Comp p pp

retractFreePromonad :: (Promonad p) => FreePromonad p :~> p
retractFreePromonad (Unit f) = arr f
retractFreePromonad (Comp p pp) = retractFreePromonad pp . p

instance (Profunctor p) => Profunctor (FreePromonad p) where
  dimap l r (Unit f) = Unit (r . f . l)
  dimap l r (Comp p q) = Comp (lmap l p) (rmap r q)
  r \\ (Unit f) = r \\ f
  r \\ Comp p q = r \\ p \\ q

instance (Profunctor p) => Promonad (FreePromonad p) where
  id = Unit id
  p . Unit f = lmap f p
  p . Comp r q = Comp r (p . q)
instance Functor FreePromonad where
  map = freeMap @Promonad
instance Promonad (Star FreePromonad) where
  id = Star (lift @Promonad)
  Star l . Star r = Star (freeComp @Promonad l r)
instance HasFree Promonad where
  type Free Promonad p = FreePromonad p
  lift = Prof \p -> p `Comp` Unit (tgt p)
  foldMap n@Prof{} = Prof retractFreePromonad . map n

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

instance HasFreeK TracedMonoidal CompactClosed INT where
  type Lift TracedMonoidal CompactClosed INT (a :: k) = I a Unit
  type Retract TracedMonoidal CompactClosed INT (I a b :: INT k) = a ** Dual b
  liftK = toInt
  retractK (Int @ap @am @bp @bm f) =
    dualObj @am //
      dualObj @bm //
        unStr $
          Str @[ap, Dual am] @[Dual am, ap] (swap @_ @ap @(Dual am)) || Str @'[] @[bm, Dual bm] (dualityUnit @bm)
            == obj @'[Dual am] || Str @[ap, bm] @[am, bp] f || obj @'[Dual bm]
            == Str @[Dual am, am] @'[] (dualityCounit @am) || obj @'[bp] || obj @'[Dual bm]