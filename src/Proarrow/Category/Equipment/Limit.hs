{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Equipment.Limit where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Bicategory
  ( Bicategory (..)
  , flipLeftAdjoint
  , flipLeftAdjointInv
  , flipRightAdjoint
  , flipRightAdjointInv
  , obj1
  )
import Proarrow.Category.Equipment (CotightAdjoint, Equipment (..), IsCotight, IsTight, TightAdjoint)
import Proarrow.Core (CAT, CategoryOf (..), (.))

-- | weighted limits
type HasLimits :: forall {s} {kk :: CAT s} {a :: s} {i :: s}. kk i a -> s -> Constraint
class (Equipment kk, Ob j) => HasLimits (j :: kk i a) k where
  type Limit (j :: kk i a) (d :: kk i k) :: kk a k
  withObLimit :: (IsTight (d :: kk i k)) => ((IsTight (Limit j d)) => r) -> r
  limit :: (IsTight (d :: kk i k)) => Limit j d `O` j ~> d
  limitUniv :: (IsTight (d :: kk i k), Ob p) => p `O` j ~> d -> p ~> Limit j d

limitToLimitAdj
  :: forall {kk} {k} {a} {b} (j :: kk a b) (c :: kk k b) (r :: kk a k)
   . (Equipment kk, HasLimits j k, IsTight r, IsCotight c)
  => I ~> c `O` Limit j r -> j ~> c `O` r
limitToLimitAdj n =
  withOb0s @kk @r $
    withOb0s @kk @c $
      withTightAdjoint @kk @c $
        withObLimit @j @_ @r $
          flipLeftAdjoint @(TightAdjoint c) @c @j @r $
            limit @j @k @r
              . ((flipLeftAdjointInv @(TightAdjoint c) @c @I @(Limit j r) n . rightUnitorInv @kk @(TightAdjoint c)) `o` obj1 @j)

limitFromLimitAdj
  :: forall {kk} {k} {a} {b} (j :: kk a b) (c :: kk k b) (r :: kk a k)
   . (Equipment kk, HasLimits j k, IsTight r, IsCotight c)
  => j ~> c `O` r -> I ~> c `O` Limit j r
limitFromLimitAdj n =
  withOb0s @kk @c $
    withTightAdjoint @kk @c $
      flipLeftAdjoint @(TightAdjoint c) @c @I @(Limit j r) $
        limitUniv @j @k @r (flipLeftAdjointInv @(TightAdjoint c) @c @j @r n) . rightUnitor @kk @(TightAdjoint c)

mapLimit
  :: forall {kk} {i} {a} (j :: kk i a) k p q
   . (HasLimits j k, IsTight p, IsTight q)
  => (p :: kk i k) ~> q -> Limit j p ~> Limit j q
mapLimit n = withOb0s @kk @p $ withObLimit @j @_ @p $ limitUniv @j @k @q (n . limit @j @k @p)

-- | weighted colimits
type HasColimits :: forall {s} {kk :: CAT s} {a :: s} {i :: s}. kk a i -> s -> Constraint
class (Equipment kk, Ob j) => HasColimits (j :: kk a i) k where
  type Colimit (j :: kk a i) (d :: kk k i) :: kk k a
  withObColimit :: (IsCotight (d :: kk k i)) => ((IsCotight (Colimit j d)) => r) -> r
  colimit :: (IsCotight (d :: kk k i)) => j `O` Colimit j d ~> d
  colimitUniv :: (IsCotight (d :: kk k i), Ob p) => (j `O` p ~> d) -> p ~> Colimit j d

colimitToLimitAdj
  :: forall {kk} {k} {a} {b} (j :: kk a b) (c :: kk k b) (r :: kk a k)
   . (Equipment kk, HasColimits j k, IsTight r, IsCotight c)
  => I ~> Colimit j c `O` r -> j ~> c `O` r
colimitToLimitAdj n =
  withOb0s @kk @c $
    withOb0s @kk @r $
      withCotightAdjoint @kk @r $
        withObColimit @j @_ @c $
          flipRightAdjoint @r @(CotightAdjoint r) @j @c $
            colimit @j @k @c
              . (obj1 @j `o` (flipRightAdjointInv @r @(CotightAdjoint r) @I @(Colimit j c) n . leftUnitorInv @kk @(CotightAdjoint r)))

colimitFromLimitAdj
  :: forall {kk} {k} {a} {b} (j :: kk a b) (c :: kk k b) (r :: kk a k)
   . (Equipment kk, HasColimits j k, IsTight r, IsCotight c)
  => j ~> c `O` r -> I ~> Colimit j c `O` r
colimitFromLimitAdj n =
  withOb0s @kk @r $
    withCotightAdjoint @kk @r $
      flipRightAdjoint @r @(CotightAdjoint r) @I @(Colimit j c) $
        colimitUniv @j @k @c (flipRightAdjointInv @r @(CotightAdjoint r) @j @c n) . leftUnitor @kk @(CotightAdjoint r)

mapColimit
  :: forall {kk} {i} {a} (j :: kk a i) k p q
   . (HasColimits j k, IsCotight p, IsCotight q)
  => (p :: kk k i) ~> q -> Colimit j p ~> Colimit j q
mapColimit n = withOb0s @kk @p $ withObColimit @j @_ @p $ colimitUniv @j @k @q (n . colimit @j @k @p)

-- type family TerminalObject (hk :: CAT s) (vk :: CAT s) :: s
-- type HasTerminalObject :: forall {s}. CAT s -> CAT s -> Constraint
-- class (HasCompanions hk vk) => HasTerminalObject (hk :: CAT s) (vk :: CAT s) where
--   type Terminate hk vk (j :: s) :: vk j (TerminalObject hk vk)
--   terminate :: (Ob0 vk j) => Obj (Terminate hk vk j)
--   termUniv :: (Ob0 vk i, Ob0 vk j, Ob (p :: hk i j)) => Sq '(p, Terminate hk vk j) '(I, Terminate hk vk i)

-- type family InitialObject (hk :: CAT s) (vk :: CAT s) :: s
-- type HasInitialObject :: forall {s}. CAT s -> CAT s -> Constraint
-- class (HasCompanions hk vk) => HasInitialObject (hk :: CAT s) (vk :: CAT s) where
--   type Initiate hk vk (j :: s) :: vk (InitialObject hk vk) j
--   initiate :: (Ob0 vk j) => Obj (Initiate hk vk j)
--   initUniv :: (Ob0 vk i, Ob0 vk j, Ob (p :: hk i j)) => Sq '(I, Initiate hk vk j) '(p, Initiate hk vk i)

-- type family Product (hk :: CAT s) (vk :: CAT s) (a :: s) (b :: s) :: s
-- type HasBinaryProducts :: forall {s}. CAT s -> CAT s -> Constraint
-- class HasBinaryProducts (hk :: CAT s) (vk :: CAT s) where
--   type Fst hk vk (i :: s) (j :: s) :: vk (Product hk vk i j) i
--   type Snd hk vk (i :: s) (j :: s) :: vk (Product hk vk i j) j
--   fstObj :: (Ob0 vk i, Ob0 vk j) => Obj (Fst hk vk i j)
--   sndObj :: (Ob0 vk i, Ob0 vk j) => Obj (Snd hk vk i j)
--   type ProdV hk vk (f :: vk k i) (g :: vk k j) :: vk k (Product hk vk i j)
--   type ProdH hk vk (p :: hk j k) (q :: hk j' k') :: hk (Product hk vk j j') (Product hk vk k k')
--   prodObj :: (Ob0 vk j, Ob0 vk a, Ob0 vk b, Ob (f :: vk j a), Ob (g :: vk j b)) => Obj (ProdV hk vk f g)
--   prodUniv
--     :: Sq '(p :: hk k k', f' :: vk k' i') '(a, f)
--     -> Sq '(p, g' :: vk k' j') '(b, g)
--     -> Sq '(p, ProdV hk vk f' g') '(ProdH hk vk a b, ProdV hk vk f g)

-- type family Coproduct (hk :: CAT s) (vk :: CAT s) (a :: s) (b :: s) :: s
-- type HasBinaryCoproducts :: forall {s}. CAT s -> CAT s -> Constraint
-- class HasBinaryCoproducts (hk :: CAT s) (vk :: CAT s) where
--   type Lft hk vk (i :: s) (j :: s) :: vk i (Coproduct hk vk i j)
--   type Rgt hk vk (i :: s) (j :: s) :: vk j (Coproduct hk vk i j)
--   lftObj :: (Ob0 vk i, Ob0 vk j) => Obj (Lft hk vk i j)
--   rgtObj :: (Ob0 vk i, Ob0 vk j) => Obj (Rgt hk vk i j)
--   type CoprodV hk vk (f :: vk i k) (g :: vk j k) :: vk (Coproduct hk vk i j) k
--   type CoprodH hk vk (p :: hk j k) (q :: hk j' k') :: hk (Coproduct hk vk j j') (Coproduct hk vk k k')
--   coprodObj :: (Ob0 vk j, Ob0 vk a, Ob0 vk b, Ob (f :: vk a j), Ob (g :: vk b j)) => Obj (CoprodV hk vk f g)
--   coprodUniv
--     :: Sq '(a :: hk i i', f' :: vk i' k') '(p :: hk k k', f :: vk i k)
--     -> Sq '(b :: hk j j', g' :: vk j' k') '(p :: hk k k', g :: vk j k)
--     -> Sq '(CoprodH hk vk a b, CoprodV hk vk f' g') '(p, CoprodV hk vk f g)