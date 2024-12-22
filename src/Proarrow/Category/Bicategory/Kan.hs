{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Kan where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory (Bicategory (..), (==), (||))
import Proarrow.Category.Equipment
  ( Equipment (..)
  , HasCompanions (..)
  , flipCompanion
  , flipCompanionInv
  , flipConjoint
  , flipConjointInv
  )
import Proarrow.Core (CAT, CategoryOf (..), Ob, Obj, Profunctor (..), Promonad (..), obj, (\\))

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

lanComonadEpsilon :: forall {kk} {c} {d} (p :: kk c d). (LeftKanExtension p p) => Lan p p ~> I
lanComonadEpsilon = lanUniv @p @p leftUnitorInv \\ iObj @kk @d

lanComonadDelta :: forall {kk} {c} {d} (p :: kk c d). (LeftKanExtension p p) => Lan p p ~> Lan p p `O` Lan p p
lanComonadDelta =
  let lpp = obj @(Lan p p)
  in lanUniv @p @p (associatorInv @_ @(Lan p p) @(Lan p p) @p . (lpp `o` lan @p @p) . lan @p @p)
      \\ iObj @kk @d
      \\ (lpp `o` lpp)

idLan :: forall f. (LeftKanExtension I f, Ob f) => f ~> Lan I f
idLan = rightUnitor . lan @I @f

lanAlongCompanion
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (LeftKanExtension (Companion hk j) f, Equipment hk vk)
  => Obj j
  -> Lan (Companion hk j) f ~> f `O` Conjoint hk j
lanAlongCompanion j =
  let f = obj @f; conJ = mapConjoint @hk j
  in lanUniv @(Companion hk j) @f
      (rightUnitorInv == f || comConUnit j == associatorInv @_ @f @(Conjoint hk j) @(Companion hk j))
      \\ (f `o` conJ)
      \\ conJ

lanAlongCompanionInv
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (LeftKanExtension (Companion hk j) f, Equipment hk vk)
  => Obj j
  -> f `O` Conjoint hk j ~> Lan (Companion hk j) f
lanAlongCompanionInv j = flipConjointInv @hk @vk @j @f @(Lan (Companion hk j) f) j (lan @(Companion hk j))

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

ranMonadEta :: forall {kk} {c} {d} (p :: kk c d). (RightKanExtension p p) => I ~> Ran p p
ranMonadEta = ranUniv @p @p leftUnitor \\ iObj @kk @d

ranMonadMu :: forall {kk} {c} {d} (p :: kk c d). (RightKanExtension p p) => Ran p p `O` Ran p p ~> Ran p p
ranMonadMu =
  let rpp = obj @(Ran p p)
  in ranUniv @p @p (ran @p @p . (rpp `o` ran @p @p) . associator @_ @(Ran p p) @(Ran p p) @p) \\ iObj @kk @d \\ (rpp `o` rpp)

composeRan
  :: forall i j f
   . (RightKanExtension j f, RightKanExtension i (Ran j f), RightKanExtension (i `O` j) f)
  => Ran i (Ran j f) ~> Ran (i `O` j) f
composeRan =
  ranUniv @(i `O` j) @f
    (ran @j @f . (ran @i @(Ran j f) `o` obj @j) . associatorInv @_ @(Ran i (Ran j f)) @i @j)

idRan :: forall f. (RightKanExtension I f, Ob f) => f ~> Ran I f
idRan = ranUniv @I @f rightUnitor

ranAlongConjoint
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (RightKanExtension (Conjoint hk j) f, Equipment hk vk)
  => Obj j
  -> Ran (Conjoint hk j) f ~> f `O` Companion hk j
ranAlongConjoint j = flipConjoint @hk @vk @j @(Ran (Conjoint hk j) f) @f j (ran @(Conjoint hk j))

ranAlongConjointInv
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (RightKanExtension (Conjoint hk j) f, Equipment hk vk)
  => Obj j
  -> f `O` Companion hk j ~> Ran (Conjoint hk j) f
ranAlongConjointInv j =
  let f = obj @f; comJ = mapCompanion @hk j
  in ranUniv @(Conjoint hk j) @f (rightUnitor . (f `o` comConCounit j) . associator @_ @f @(Companion hk j) @(Conjoint hk j))
      \\ (f `o` comJ)
      \\ comJ

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
liftComonadEpsilon = liftUniv @p @p rightUnitorInv \\ iObj @kk @d

liftComonadDelta :: forall {kk} {c} {d} (p :: kk d c). (LeftKanLift p p) => Lift p p ~> Lift p p `O` Lift p p
liftComonadDelta =
  let lpp = obj @(Lift p p)
  in liftUniv @p @p (associator @_ @p @(Lift p p) @(Lift p p) . (lift @p @p `o` lpp) . lift @p @p)
      \\ iObj @kk @d
      \\ (lpp `o` lpp)

idLift :: forall f. (LeftKanLift I f, Ob f) => f ~> Lift I f
idLift = leftUnitor . lift @I @f

liftAlongConjoint
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (LeftKanLift (Conjoint hk j) f, Equipment hk vk)
  => Obj j
  -> Lift (Conjoint hk j) f ~> Companion hk j `O` f
liftAlongConjoint j =
  let f = obj @f; comJ = mapCompanion @hk j
  in liftUniv @(Conjoint hk j) @f
      (associator @_ @(Conjoint hk j) @(Companion hk j) @f . (comConUnit j `o` f) . leftUnitorInv)
      \\ (comJ `o` f)
      \\ comJ

liftAlongConjointInv
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (LeftKanLift (Conjoint hk j) f, Equipment hk vk)
  => Obj j
  -> Companion hk j `O` f ~> Lift (Conjoint hk j) f
liftAlongConjointInv j = flipCompanionInv @hk @vk @j @f @(Lift (Conjoint hk j) f) j (lift @(Conjoint hk j))

type p <| j = Rift j p
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
riftMonadEta = riftUniv @p @p rightUnitor \\ iObj @kk @d

riftMonadMu :: forall {kk} {c} {d} (p :: kk d c). (RightKanLift p p) => Rift p p `O` Rift p p ~> Rift p p
riftMonadMu =
  let rpp = obj @(Rift p p)
  in riftUniv @p @p (rift @p @p . (rift @p @p `o` rpp) . associatorInv @_ @p @(Rift p p) @(Rift p p))
      \\ iObj @kk @d
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

riftAlongCompanion
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (RightKanLift (Companion hk j) f, Equipment hk vk)
  => Obj j
  -> Rift (Companion hk j) f ~> Conjoint hk j `O` f
riftAlongCompanion j = flipCompanion @hk @vk @j @(Rift (Companion hk j) f) @f j (rift @(Companion hk j))

riftAlongCompanionInv
  :: forall {i} {k} hk vk (j :: vk i k) f
   . (RightKanLift (Companion hk j) f, Equipment hk vk)
  => Obj j
  -> Conjoint hk j `O` f ~> Rift (Companion hk j) f
riftAlongCompanionInv j =
  let f = obj @f; conJ = mapConjoint @hk j
  in riftUniv @(Companion hk j) @f
      (leftUnitor . (comConCounit j `o` f) . associatorInv @_ @(Companion hk j) @(Conjoint hk j) @f)
      \\ (conJ `o` f)
      \\ conJ