{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Equipment.Limit where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Equipment (HasCompanions (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, Promonad (..), obj, (//))

-- | weighted limits
type HasLimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk i a -> s -> Constraint
class (HasCompanions hk vk, Ob j) => HasLimits vk (j :: hk i a) k where
  type Limit (j :: hk i a) (d :: vk i k) :: vk a k
  limitObj :: Ob (d :: vk i k) => Obj (Limit j d)
  limit :: (Ob (d :: vk i k)) => Companion hk (Limit j d) `O` j ~> Companion hk d
  limitUniv :: (Ob (d :: vk i k), Ob p) => Companion hk p `O` j ~> Companion hk d -> p ~> Limit j d

-- > i--d--k
-- > |  v  |
-- > j--@  |
-- > |  v  |
-- > a--l--k

-- lift :: f ~> j `O` Lift j f

-- > i--d--k
-- > |  v  |
-- > | /@\ |
-- > | v v |
-- > a-j-l-k


-- > i--d--k    a--p--k
-- > |  v  |    |  |  |
-- > j--@  | => |  @  |
-- > |  v  |    |  |  |
-- > a--p--k    a--l--k

-- rightAdjointPreservesLimits
--   :: forall {k} {k'} {i} {a} (f :: k' +-> k) (g :: k +-> k') (d :: i +-> k) (j :: i +-> a)
--    . (Adjunction f g, Representable d, Representable g, HasLimits j k, HasLimits j k')
--   => Limit j (g :.: d) :~> g :.: Limit j d
-- rightAdjointPreservesLimits lim =
--   lim // case unit @f @g of
--     g :.: f ->
--       g
--         :.: limitUniv @j @k @d
--           (\((f' :.: lim') :.: j) -> case limit @j @k' @(g :.: d) (lim' :.: j) of g' :.: d -> lmap (counit (f' :.: g')) d)
--           (f :.: lim)

-- > a--l'-k'----k'
-- > |  v  |     |
-- > |  |  | /@\ |
-- > |  |  | v v |
-- > |  |  k'f-g-k'
-- > |  |  /   v |
-- > |  | /    | |
-- > |  @/     | |
-- > |  |      | |
-- > a--l---k--g-k'

-- > i--d--k    a-l'f-k
-- > |  v  |    |  |  |
-- > j--@  | => |  @  |
-- > |  v  |    |  |  |
-- > a-l'f-k    a--l--k

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
        (compFromCompose g d . (cg `o` limit @vk @j @k @d) . associator cg (mapCompanion l) j . (compToCompose g l `o` j))

-- > i-d-k-g-k'    a-l-g-k'
-- > | v | v |     | v v |
-- > j-@ | | |  => | \@/ |
-- > | v | v |     |  |  |
-- > a-l-k-g-k'    a--l'-k'

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
