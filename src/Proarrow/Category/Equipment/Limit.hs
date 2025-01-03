{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Equipment.Limit where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory (Bicategory (..), associator')
import Proarrow.Category.Equipment (HasCompanions (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, Promonad (..), obj, (//))

-- | weighted limits
type HasLimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk i a -> s -> Constraint
class (HasCompanions hk vk, Ob j) => HasLimits vk (j :: hk i a) k where
  type Limit (j :: hk i a) (d :: vk i k) :: vk a k
  limitObj :: Ob (d :: vk i k) => Obj (Limit j d)
  limit :: (Ob (d :: vk i k)) => Companion hk (Limit j d) `O` j ~> Companion hk d
  limitUniv :: (Ob (d :: vk i k), Ob p) => Companion hk p `O` j ~> Companion hk d -> p ~> Limit j d

-- lift :: f ~> j `O` Lift j f

rightAdjointPreservesLimitsInv
  :: forall {hk} {vk} {k} {k'} {i} {a} (g :: vk k k') (d :: vk i k) (j :: hk i a)
   . (Ob d, Ob g, HasLimits vk j k, HasLimits vk j k', Ob0 vk i, Ob0 vk k, Ob0 vk k', Ob0 vk a)
  => g `O` Limit j d ~> Limit j (g `O` d)
rightAdjointPreservesLimitsInv =
  let
    d = obj @d
    g = obj @g
    cg = mapCompanion @hk g
    j = obj @j
    l = limitObj @vk @j @k @d
  in
    (g `o` d)
      // (g `o` l)
      // limitUniv @vk @j @k' @(g `O` d)
        (compFromCompose g d . (cg `o` limit @vk @j @k @d) . associator' cg (mapCompanion l) j . (compToCompose g l `o` j))

-- | weighted colimits
type HasColimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk a i -> s -> Constraint
class (HasCompanions hk vk, Ob j) => HasColimits vk (j :: hk a i) k where
  type Colimit (j :: hk a i) (d :: vk i k) :: vk a k
  colimit :: (Ob (d :: vk i k)) => Companion hk d `O` j ~> Companion hk (Colimit j d)
  colimitUniv :: (Ob (d :: vk i k), Ob p) => Companion hk d `O` j ~> Companion hk p -> Colimit j d ~> p

-- > a--c--k
-- > |  v  |
-- > j--@  |
-- > |  v  |
-- > i--d--k

-- lan :: f ~> Lan j f `O` j

-- > a--c--k
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > i-j-d-k
