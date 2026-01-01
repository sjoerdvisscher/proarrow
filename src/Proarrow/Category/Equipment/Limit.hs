{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Equipment.Limit where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Bicategory (Bicategory (..), obj1)
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..), Sq, flipCompanion, flipCompanionInv)
import Proarrow.Core (CAT, CategoryOf (..), Obj, (.))

-- | weighted limits
type HasLimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk i a -> s -> Constraint
class (HasCompanions hk vk, Ob j) => HasLimits vk (j :: hk i a) k where
  type Limit (j :: hk i a) (d :: vk i k) :: vk a k
  withObLimit :: (Ob (d :: vk i k)) => ((Ob (Limit j d)) => r) -> r
  limit :: (Ob (d :: vk i k)) => Companion hk (Limit j d) `O` j ~> Companion hk d
  limitUniv :: (Ob (d :: vk i k), Ob p) => p `O` j ~> Companion hk d -> p ~> Companion hk (Limit j d)

toLimitAdj
  :: forall {hk} {vk} {k} {a} {b} (j :: hk a b) (c :: vk b k) (r :: vk a k)
   . (Equipment hk vk, HasLimits vk j k, Ob r, Ob c)
  => Companion hk c ~> Companion hk (Limit j r) -> j ~> Conjoint hk c `O` Companion hk r
toLimitAdj n =
  withOb0s @vk @r $
    flipCompanion @c @j @(Companion hk r) (limit @vk @j @k @r . (n `o` obj1 @j)) \\\ n

fromLimitAdj
  :: forall {hk} {vk} {k} {a} {b} (j :: hk a b) (c :: vk b k) (r :: vk a k)
   . (Equipment hk vk, HasLimits vk j k, Ob r, Ob c)
  => j ~> Conjoint hk c `O` Companion hk r -> Companion hk c ~> Companion hk (Limit j r)
fromLimitAdj n =
  withObCompanion @hk @vk @r $
    withObCompanion @hk @vk @c $
      limitUniv @vk @j @k @r (flipCompanionInv @c @j @(Companion hk r) n) \\\ n

mapLimit
  :: forall {hk} {vk} {i} {a} (j :: hk i a) k p q
   . (HasLimits vk j k)
  => (p :: vk i k) ~> q -> Companion hk (Limit j p) ~> Companion hk (Limit j q)
mapLimit n =
  ( withObLimit @vk @j @k @p $
      withObCompanion @hk @vk @(Limit j p) $
        limitUniv @vk @j @k @q (mapCompanion n . limit @vk @j @k @p)
  )
    \\\ n

-- | weighted colimits
type HasColimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk a i -> s -> Constraint
class (Equipment hk vk, Ob j) => HasColimits vk (j :: hk a i) k where
  type Colimit (j :: hk a i) (d :: vk i k) :: vk a k
  withObColimit :: (Ob (d :: vk i k)) => ((Ob (Colimit j d)) => r) -> r
  colimit :: (Ob (d :: vk i k)) => j `O` Conjoint hk (Colimit j d) ~> Conjoint hk d
  colimitUniv :: (Ob (d :: vk i k), Ob p) => (j `O` p ~> Conjoint hk d) -> p ~> Conjoint hk (Colimit j d)

type family TerminalObject (hk :: CAT s) (vk :: CAT s) :: s
type HasTerminalObject :: forall {s}. CAT s -> CAT s -> Constraint
class (HasCompanions hk vk) => HasTerminalObject (hk :: CAT s) (vk :: CAT s) where
  type Terminate hk vk (j :: s) :: vk j (TerminalObject hk vk)
  terminate :: (Ob0 vk j) => Obj (Terminate hk vk j)
  termUniv :: (Ob0 vk i, Ob0 vk j, Ob (p :: hk i j)) => Sq '(p, Terminate hk vk j) '(I, Terminate hk vk i)

type family InitialObject (hk :: CAT s) (vk :: CAT s) :: s
type HasInitialObject :: forall {s}. CAT s -> CAT s -> Constraint
class (HasCompanions hk vk) => HasInitialObject (hk :: CAT s) (vk :: CAT s) where
  type Initiate hk vk (j :: s) :: vk (InitialObject hk vk) j
  initiate :: (Ob0 vk j) => Obj (Initiate hk vk j)
  initUniv :: (Ob0 vk i, Ob0 vk j, Ob (p :: hk i j)) => Sq '(I, Initiate hk vk j) '(p, Initiate hk vk i)

type family Product (hk :: CAT s) (vk :: CAT s) (a :: s) (b :: s) :: s
type HasBinaryProducts :: forall {s}. CAT s -> CAT s -> Constraint
class HasBinaryProducts (hk :: CAT s) (vk :: CAT s) where
  type Fst hk vk (i :: s) (j :: s) :: vk (Product hk vk i j) i
  type Snd hk vk (i :: s) (j :: s) :: vk (Product hk vk i j) j
  fstObj :: (Ob0 vk i, Ob0 vk j) => Obj (Fst hk vk i j)
  sndObj :: (Ob0 vk i, Ob0 vk j) => Obj (Snd hk vk i j)
  type ProdV hk vk (f :: vk k i) (g :: vk k j) :: vk k (Product hk vk i j)
  type ProdH hk vk (p :: hk j k) (q :: hk j' k') :: hk (Product hk vk j j') (Product hk vk k k')
  prodObj :: (Ob0 vk j, Ob0 vk a, Ob0 vk b, Ob (f :: vk j a), Ob (g :: vk j b)) => Obj (ProdV hk vk f g)
  prodUniv
    :: Sq '(p :: hk k k', f' :: vk k' i') '(a, f)
    -> Sq '(p, g' :: vk k' j') '(b, g)
    -> Sq '(p, ProdV hk vk f' g') '(ProdH hk vk a b, ProdV hk vk f g)

type family Coproduct (hk :: CAT s) (vk :: CAT s) (a :: s) (b :: s) :: s
type HasBinaryCoproducts :: forall {s}. CAT s -> CAT s -> Constraint
class HasBinaryCoproducts (hk :: CAT s) (vk :: CAT s) where
  type Lft hk vk (i :: s) (j :: s) :: vk i (Coproduct hk vk i j)
  type Rgt hk vk (i :: s) (j :: s) :: vk j (Coproduct hk vk i j)
  lftObj :: (Ob0 vk i, Ob0 vk j) => Obj (Lft hk vk i j)
  rgtObj :: (Ob0 vk i, Ob0 vk j) => Obj (Rgt hk vk i j)
  type CoprodV hk vk (f :: vk i k) (g :: vk j k) :: vk (Coproduct hk vk i j) k
  type CoprodH hk vk (p :: hk j k) (q :: hk j' k') :: hk (Coproduct hk vk j j') (Coproduct hk vk k k')
  coprodObj :: (Ob0 vk j, Ob0 vk a, Ob0 vk b, Ob (f :: vk a j), Ob (g :: vk b j)) => Obj (CoprodV hk vk f g)
  coprodUniv
    :: Sq '(a :: hk i i', f' :: vk i' k') '(p :: hk k k', f :: vk i k)
    -> Sq '(b :: hk j j', g' :: vk j' k') '(p :: hk k k', g :: vk j k)
    -> Sq '(CoprodH hk vk a b, CoprodV hk vk f' g') '(p, CoprodV hk vk f g)