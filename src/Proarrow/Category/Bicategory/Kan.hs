{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Kan where

import Data.Functor.Compose (Compose (..))
import Data.Kind (Constraint, Type)
import Prelude (($))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Core (CAT, CategoryOf (..), Ob, Profunctor (..), Promonad (..), obj, (\\))
import Proarrow.Functor (Functor, map)

type LeftKanExtension :: forall {k} {kk :: CAT k} {c} {d} {e}. kk d c -> kk e c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Lan j f)) => LeftKanExtension (j :: kk d c) (f :: kk e c) where
  type Lan j f :: kk e d
  lan :: f ~> j `O` Lan j f
  lanUniv :: (Ob g) => (f ~> j `O` g) -> Lan j f ~> g

mapLan :: forall j f g. (LeftKanExtension j f, LeftKanExtension j g) => (f ~> g) -> Lan j f ~> Lan j g
mapLan fg = lanUniv @j (lan @j . fg)

rebaseLan :: forall f i j. (LeftKanExtension j f, LeftKanExtension i f) => (i ~> j) -> Lan j f ~> Lan i f
rebaseLan ij = lanUniv @j ((ij `o` obj @(Lan i f)) . lan @i @f)

dimapLan :: forall i j f g. (LeftKanExtension j f, LeftKanExtension i g) => (i ~> j) -> (f ~> g) -> (Lan j f ~> Lan i g)
dimapLan ij fg = lanUniv @j ((ij `o` obj @(Lan i g)) . lan @i . fg) \\ ij

type RightKanExtension :: forall {k} {kk :: CAT k} {c} {d} {e}. kk d c -> kk e c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Ran j f)) => RightKanExtension (j :: kk d c) (f :: kk e c) where
  type Ran j f :: kk e d
  ran :: j `O` Ran j f ~> f
  ranUniv :: (Ob g) => (j `O` g ~> f) -> g ~> Ran j f

mapRan :: forall j f g. (RightKanExtension j f, RightKanExtension j g) => (f ~> g) -> Ran j f ~> Ran j g
mapRan fg = ranUniv @j (fg . ran @j)

rebaseRan :: forall f i j. (RightKanExtension j f, RightKanExtension i f) => (i ~> j) -> Ran j f ~> Ran i f
rebaseRan ij = ranUniv @i @f (ran @j . (ij `o` obj @(Ran j f)))

dimapRan
  :: forall i j f g. (RightKanExtension j f, RightKanExtension i g) => (i ~> j) -> (f ~> g) -> (Ran j f ~> Ran i g)
dimapRan ij fg = ranUniv @i (fg . ran @j . (ij `o` obj @(Ran j f))) \\ ij

type LeftKanLift :: forall {k} {kk :: CAT k} {c} {d} {e}. kk c d -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Lift j f)) => LeftKanLift (j :: kk c d) (f :: kk c e) where
  type Lift j f :: kk d e
  lift :: f ~> Lift j f `O` j
  liftUniv :: (Ob g) => (f ~> g `O` j) -> Lift j f ~> g

mapLift :: forall j f g. (LeftKanLift j f, LeftKanLift j g) => (f ~> g) -> Lift j f ~> Lift j g
mapLift fg = liftUniv @j (lift @j . fg)

rebaseLift :: forall f i j. (LeftKanLift j f, LeftKanLift i f) => (i ~> j) -> Lift j f ~> Lift i f
rebaseLift ij = liftUniv @j ((obj @(Lift i f) `o` ij) . lift @i @f)

dimapLift :: forall i j f g. (LeftKanLift j f, LeftKanLift i g) => (i ~> j) -> (f ~> g) -> (Lift j f ~> Lift i g)
dimapLift ij fg = liftUniv @j ((obj @(Lift i g) `o` ij) . lift @i . fg) \\ ij

type RightKanLift :: forall {k} {kk :: CAT k} {c} {d} {e}. kk c d -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Rift j f)) => RightKanLift (j :: kk c d) (f :: kk c e) where
  type Rift j f :: kk d e
  rift :: Rift j f `O` j ~> f
  riftUniv :: (Ob g) => (g `O` j ~> f) -> g ~> Rift j f

mapRift :: forall j f g. (RightKanLift j f, RightKanLift j g) => (f ~> g) -> Rift j f ~> Rift j g
mapRift fg = riftUniv @j (fg . rift @j)

rebaseRift :: forall f i j. (RightKanLift j f, RightKanLift i f) => (i ~> j) -> Rift j f ~> Rift i f
rebaseRift ij = riftUniv @i (rift @j @f . (obj @(Rift j f) `o` ij))

dimapRift :: forall i j f g. (RightKanLift j f, RightKanLift i g) => (i ~> j) -> (f ~> g) -> (Rift j f ~> Rift i g)
dimapRift ij fg = riftUniv @i (fg . rift @j . (obj @(Rift j f) `o` ij)) \\ ij

newtype HaskRan g h a = Ran {runRan :: forall b. (a -> g b) -> h b}
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
