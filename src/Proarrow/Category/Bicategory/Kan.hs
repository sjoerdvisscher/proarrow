{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.Kan where

import Data.Kind (Constraint, Type)

import Proarrow.Category.Bicategory (Bicategory(..))
import Proarrow.Category.Bicategory.MonoidalAsBi (MonK(..), Mon2 (..))
import Proarrow.Core (CAT, Ob, obj, CategoryOf (..), Promonad (..))
import Data.Functor.Compose (Compose(..))
import Prelude (($))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Functor (map, Functor)


type LeftKanExtension :: forall {k} {kk :: CAT k} {c} {d} {e}. kk c d -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Lan j f)) => LeftKanExtension (j :: kk c d) (f :: kk c e) where
  type Lan j f :: kk d e
  lan :: f ~> j `O` Lan j f
  lanUniv :: Ob g => (f ~> j `O` g) -> Lan j f ~> g

mapLan :: forall j f g. (LeftKanExtension j f, LeftKanExtension j g) => (f ~> g) -> Lan j f ~> Lan j g
mapLan fg = lanUniv @j (lan @j . fg)

rebaseLan :: forall i j f. (LeftKanExtension j f, LeftKanExtension i f) => (i ~> j) -> Lan j f ~> Lan i f
rebaseLan ij = lanUniv @j ((ij `o` obj @(Lan i f)) . lan @i @f)


type RightKanExtension :: forall {k} {kk :: CAT k} {c} {d} {e}. kk c d -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Ran j f)) => RightKanExtension (j :: kk c d) (f :: kk c e) where
  type Ran j f :: kk d e
  ran :: j `O` Ran j f ~> f
  ranUniv :: Ob g => (j `O` g ~> f) -> g ~> Ran j f

mapRan :: forall j f g. (RightKanExtension j f, RightKanExtension j g) => (f ~> g) -> Ran j f ~> Ran j g
mapRan fg = ranUniv @j (fg . ran @j)

rebaseRan :: forall i j f. (RightKanExtension j f, RightKanExtension i f) => (i ~> j) -> Ran j f ~> Ran i f
rebaseRan ij = ranUniv @i @f (ran @j . (ij `o` obj @(Ran j f)))


type LeftKanLift :: forall {k} {kk :: CAT k} {c} {d} {e}. kk d c -> kk e c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Lift j f)) => LeftKanLift (j :: kk d c) (f :: kk e c) where
  type Lift j f :: kk e d
  lift :: f ~> Lift j f `O` j
  liftUniv :: Ob g => (f ~> g `O` j) -> Lift j f ~> g

mapLift :: forall j f g. (LeftKanLift j f, LeftKanLift j g) => (f ~> g) -> Lift j f ~> Lift j g
mapLift fg = liftUniv @j (lift @j . fg)

rebaseLift :: forall i j f. (LeftKanLift j f, LeftKanLift i f) => (i ~> j) -> Lift j f ~> Lift i f
rebaseLift ij = liftUniv @j ((obj @(Lift i f) `o` ij) . lift @i @f)


type RightKanLift :: forall {k} {kk :: CAT k} {c} {d} {e}. kk d c -> kk e c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Rift j f)) => RightKanLift (j :: kk d c) (f :: kk e c) where
  type Rift j f :: kk e d
  rift :: Rift j f `O` j ~> f
  riftUniv :: Ob g => (g `O` j ~> f) -> g ~> Rift j f

mapRift :: forall j f g. (RightKanLift j f, RightKanLift j g) => (f ~> g) -> Rift j f ~> Rift j g
mapRift fg = riftUniv @j (fg . rift @j)

rebaseRift :: forall i j f. (RightKanLift j f, RightKanLift i f) => (i ~> j) -> Rift j f ~> Rift i f
rebaseRift ij = riftUniv @i (rift @j @f . (obj @(Rift j f) `o` ij))


newtype HaskRan g h a = Ran { runRan :: forall b. (a -> g b) -> h b }
instance Functor (HaskRan g h) where
  map f (Ran k) = Ran $ \g -> k (g . f)
instance (Functor j, Functor f) => RightKanExtension (MK (j :: Type -> Type)) (MK f) where
  type Ran (MK j) (MK f) = MK (HaskRan j f)
  ran = Mon2 $ Nat \(Compose rj) -> runRan rj id
  ranUniv (Mon2 (Nat n)) = Mon2 $ Nat \g -> Ran \f -> n (Compose (map f g))

data HaskLan j f a where
  Lan :: (j b -> a) -> f b -> HaskLan j f a
instance Functor (HaskLan j f) where
  map g (Lan k f) = Lan (g . k) f
instance (Functor j, Functor f) => LeftKanExtension (MK (j :: Type -> Type)) (MK f) where
  type Lan (MK j) (MK f) = MK (HaskLan j f)
  lan = Mon2 $ Nat (Compose . Lan id)
  lanUniv (Mon2 (Nat n)) = Mon2 $ Nat \(Lan k f) -> map k (getCompose (n f))