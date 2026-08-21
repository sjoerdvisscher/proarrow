{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Kan where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory
  ( Adjunction (..)
  , Bicategory (..)
  , Comonad (..)
  , Monad (..)
  , rightUnitorInvWith
  , rightUnitorWith
  , (==)
  , (||), flipRightAdjointInv, flipRightAdjoint, flipLeftAdjointInv, flipLeftAdjoint
  )

import Proarrow.Core (CAT, CategoryOf (..), Ob, Profunctor (..), Promonad (..), obj, (\\))

type LeftKanExtension :: forall {k} {kk :: CAT k} {c} {d} {e}. kk c d -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Lan j f)) => LeftKanExtension (j :: kk c d) (f :: kk c e) where
  type Lan j f :: kk d e
  lan :: f ~> Lan j f `O` j
  lanUniv :: (Ob g) => (f ~> g `O` j) -> Lan j f ~> g

mapLan :: forall j f g. (LeftKanExtension j f, LeftKanExtension j g) => (f ~> g) -> Lan j f ~> Lan j g
mapLan fg = lanUniv @j (lan @j . fg)

rebaseLan :: forall f i j. (LeftKanExtension j f, LeftKanExtension i f) => (i ~> j) -> Lan j f ~> Lan i f
rebaseLan ij = lanUniv @j ((obj @(Lan i f) `o` ij) . lan @i @f)

dimapLan :: forall i j f g. (LeftKanExtension j f, LeftKanExtension i g) => (i ~> j) -> (f ~> g) -> (Lan j f ~> Lan i g)
dimapLan ij fg = lanUniv @j ((obj @(Lan i g) `o` ij) . lan @i . fg) \\ ij

type Density p = Lan p p

lanComonadEpsilon :: forall {kk} {c} {d} (p :: kk c d). (LeftKanExtension p p) => Density p ~> I
lanComonadEpsilon = lanUniv @p @p leftUnitorInv

lanComonadDelta :: forall {kk} {c} {d} (p :: kk c d). (LeftKanExtension p p) => Density p ~> Density p `O` Density p
lanComonadDelta =
  let lpp = obj @(Lan p p)
  in lanUniv @p @p (associatorInv @_ @(Lan p p) @(Lan p p) @p . (lpp `o` lan @p @p) . lan @p @p)
       \\ (lpp `o` lpp)

-- | Density is the "mother of all comonads"
coinj :: forall p. (Comonad p, LeftKanExtension p p) => p ~> Density p
coinj = rightUnitorWith (epsilon @p) id . lan @p @p

corun :: forall p. (Comonad p, LeftKanExtension p p) => Density p ~> p
corun = lanUniv @p @p delta

idLan :: forall f. (LeftKanExtension I f, Ob f) => f ~> Lan I f
idLan = rightUnitor . lan @I @f

lanAlongLeftAdjoint
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (LeftKanExtension j f, Adjunction j j', Ob j, Ob j')
  => Lan j f ~> f `O` j'
lanAlongLeftAdjoint =
  withOb2 @kk @f @j'
    (lanUniv @j @f (rightUnitorInv == obj @f || unit @j @j' == associatorInv @_ @f @j' @j))

lanAlongLeftAdjointInv
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (LeftKanExtension j f, Adjunction j j', Ob j, Ob j')
  => f `O` j' ~> Lan j f
lanAlongLeftAdjointInv = flipRightAdjointInv @j @j' (lan @j @f)

type j |> p = Ran j p
type RightKanExtension :: forall {k} {kk :: CAT k} {c} {d} {e}. kk c d -> kk c e -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Ran j f)) => RightKanExtension (j :: kk c d) (f :: kk c e) where
  type Ran j f :: kk d e
  ran :: Ran j f `O` j ~> f
  ranUniv :: (Ob g) => (g `O` j ~> f) -> g ~> Ran j f

mapRan :: forall j f g. (RightKanExtension j f, RightKanExtension j g) => (f ~> g) -> Ran j f ~> Ran j g
mapRan fg = ranUniv @j (fg . ran @j)

rebaseRan :: forall f i j. (RightKanExtension j f, RightKanExtension i f) => (i ~> j) -> Ran j f ~> Ran i f
rebaseRan ij = ranUniv @i @f (ran @j . (obj @(Ran j f) `o` ij))

dimapRan
  :: forall i j f g. (RightKanExtension j f, RightKanExtension i g) => (i ~> j) -> (f ~> g) -> (Ran j f ~> Ran i g)
dimapRan ij fg = ranUniv @i (fg . ran @j . (obj @(Ran j f) `o` ij)) \\ ij

type Codensity p = Ran p p

ranMonadEta :: forall {kk} {c} {d} (p :: kk c d). (RightKanExtension p p) => I ~> Codensity p
ranMonadEta = ranUniv @p @p leftUnitor

ranMonadMu :: forall {kk} {c} {d} (p :: kk c d). (RightKanExtension p p) => Codensity p `O` Codensity p ~> Codensity p
ranMonadMu =
  let rpp = obj @(Ran p p)
  in ranUniv @p @p (ran @p @p . (rpp `o` ran @p @p) . associator @_ @(Ran p p) @(Ran p p) @p) \\ (rpp `o` rpp)

-- | Codensity is the "mother of all monads"
inj :: forall p. (Monad p, RightKanExtension p p) => p ~> Codensity p
inj = ranUniv @p @p mu

run :: forall p. (Monad p, RightKanExtension p p) => Codensity p ~> p
run = ran @p @p . rightUnitorInvWith (eta @p) id

composeRan
  :: forall i j f
   . (RightKanExtension j f, RightKanExtension i (Ran j f), RightKanExtension (i `O` j) f)
  => Ran i (Ran j f) ~> Ran (i `O` j) f
composeRan =
  ranUniv @(i `O` j) @f
    (ran @j @f . (ran @i @(Ran j f) `o` obj @j) . associatorInv @_ @(Ran i (Ran j f)) @i @j)

idRan :: forall f. (RightKanExtension I f, Ob f) => f ~> Ran I f
idRan = ranUniv @I @f rightUnitor

ranAlongRightAdjoint
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (RightKanExtension j' f, Adjunction j j', Ob j, Ob j')
  => Ran j' f ~> f `O` j
ranAlongRightAdjoint = flipRightAdjoint @j @j' (ran @j' @f)

ranAlongRightAdjointInv
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (RightKanExtension j' f, Adjunction j j', Ob j, Ob j')
  => f `O` j ~> Ran j' f
ranAlongRightAdjointInv =
  withOb2 @kk @f @j
    (ranUniv @j' @f (associator @_ @f @j @j' == obj @f || counit @j @j' == rightUnitor))

type LeftKanLift :: forall {k} {kk :: CAT k} {c} {d} {e}. kk d c -> kk e c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Lift j f)) => LeftKanLift (j :: kk d c) (f :: kk e c) where
  type Lift j f :: kk e d
  lift :: f ~> j `O` Lift j f
  liftUniv :: (Ob g) => (f ~> j `O` g) -> Lift j f ~> g

mapLift :: forall j f g. (LeftKanLift j f, LeftKanLift j g) => (f ~> g) -> Lift j f ~> Lift j g
mapLift fg = liftUniv @j (lift @j . fg)

rebaseLift :: forall f i j. (LeftKanLift j f, LeftKanLift i f) => (i ~> j) -> Lift j f ~> Lift i f
rebaseLift ij = liftUniv @j ((ij `o` obj @(Lift i f)) . lift @i @f)

dimapLift :: forall i j f g. (LeftKanLift j f, LeftKanLift i g) => (i ~> j) -> (f ~> g) -> (Lift j f ~> Lift i g)
dimapLift ij fg = liftUniv @j ((ij `o` obj @(Lift i g)) . lift @i . fg) \\ ij

liftComonadEpsilon :: forall {kk} {c} {d} (p :: kk d c). (LeftKanLift p p) => Lift p p ~> I
liftComonadEpsilon = liftUniv @p @p rightUnitorInv

liftComonadDelta :: forall {kk} {c} {d} (p :: kk d c). (LeftKanLift p p) => Lift p p ~> Lift p p `O` Lift p p
liftComonadDelta =
  let lpp = obj @(Lift p p)
  in liftUniv @p @p (associator @_ @p @(Lift p p) @(Lift p p) . (lift @p @p `o` lpp) . lift @p @p)
       \\ (lpp `o` lpp)

idLift :: forall f. (LeftKanLift I f, Ob f) => f ~> Lift I f
idLift = leftUnitor . lift @I @f

liftAlongRightAdjoint
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (Ob j, Ob j', LeftKanLift j' f, Adjunction j j')
  => Lift j' f ~> j `O` f
liftAlongRightAdjoint =
  withOb2 @kk @j @f
    (liftUniv @j' @f (leftUnitorInv == unit @j @j' || obj @f == associator @_ @j' @j @f))

liftAlongRightAdjointInv
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (Ob j, Ob j', LeftKanLift j' f, Adjunction j j')
  => j `O` f ~> Lift j' f
liftAlongRightAdjointInv = flipLeftAdjointInv @j @j' (lift @j' @f)

type f <| j = Rift j f
type RightKanLift :: forall {k} {kk :: CAT k} {c} {d} {e}. kk d c -> kk e c -> Constraint
class (Bicategory kk, Ob0 kk c, Ob0 kk d, Ob0 kk e, Ob f, Ob j, Ob (Rift j f)) => RightKanLift (j :: kk d c) (f :: kk e c) where
  type Rift j f :: kk e d
  rift :: j `O` Rift j f ~> f
  riftUniv :: (Ob g) => (j `O` g ~> f) -> g ~> Rift j f

mapRift :: forall j f g. (RightKanLift j f, RightKanLift j g) => (f ~> g) -> Rift j f ~> Rift j g
mapRift fg = riftUniv @j (fg . rift @j)

rebaseRift :: forall f i j. (RightKanLift j f, RightKanLift i f) => (i ~> j) -> Rift j f ~> Rift i f
rebaseRift ij = riftUniv @i (rift @j @f . (ij `o` obj @(Rift j f)))

dimapRift :: forall i j f g. (RightKanLift j f, RightKanLift i g) => (i ~> j) -> (f ~> g) -> (Rift j f ~> Rift i g)
dimapRift ij fg = riftUniv @i (fg . rift @j . (ij `o` obj @(Rift j f))) \\ ij

riftMonadEta :: forall {kk} {c} {d} (p :: kk d c). (RightKanLift p p) => I ~> Rift p p
riftMonadEta = riftUniv @p @p rightUnitor

riftMonadMu :: forall {kk} {c} {d} (p :: kk d c). (RightKanLift p p) => Rift p p `O` Rift p p ~> Rift p p
riftMonadMu =
  let rpp = obj @(Rift p p)
  in riftUniv @p @p (rift @p @p . (rift @p @p `o` rpp) . associatorInv @_ @p @(Rift p p) @(Rift p p))
       \\ (rpp `o` rpp)

composeRift
  :: forall i j f
   . (RightKanLift j f, RightKanLift i (Rift j f), RightKanLift (j `O` i) f)
  => Rift i (Rift j f) ~> Rift (j `O` i) f
composeRift =
  riftUniv @(j `O` i) @f
    (rift @j @f . (obj @j `o` rift @i @(Rift j f)) . associator @_ @j @i @(Rift i (Rift j f)))

idRift :: forall f. (RightKanLift I f, Ob f) => f ~> Rift I f
idRift = riftUniv @I @f leftUnitor

riftAlongLeftAdjoint
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (RightKanLift j f, Adjunction j j', Ob j, Ob j')
  => Rift j f ~> j' `O` f
riftAlongLeftAdjoint = flipLeftAdjoint @j @j' (rift @j @f)

riftAlongLeftAdjointInv
  :: forall {i} {k} kk (j :: kk i k) j' f
   . (RightKanLift j f, Adjunction j j', Ob j, Ob j')
  => j' `O` f ~> Rift j f
riftAlongLeftAdjointInv =
  withOb2 @kk @j' @f
    (riftUniv @j @f (associatorInv @_ @j @j' @f == counit @j @j' || obj @f == leftUnitor))