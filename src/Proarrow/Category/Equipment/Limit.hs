{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Equipment.Limit where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Equipment (Equipment (..), HasCompanions (..))
import Proarrow.Core (CAT, CategoryOf (..))

-- | weighted limits
type HasLimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk i a -> s -> Constraint
class (Equipment hk vk, Ob j) => HasLimits vk (j :: hk i a) k where
  type Limit (j :: hk i a) (d :: vk i k) :: vk a k
  limit :: (Ob (d :: vk i k)) => Companion hk vk (Limit j d) `O` j ~> Companion hk vk d
  limitUniv :: (Ob (d :: vk i k), Ob p) => Companion hk vk p `O` j ~> Companion hk vk d -> p ~> Limit j d

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

-- rightAdjointPreservesLimitsInv
--   :: forall {hk} {vk} {k} {k'} {i} {a} (g :: vk k k') (d :: vk i k) (j :: hk i a)
--    . (Ob d, Ob g, HasLimits vk j k, HasLimits vk j k')
--   => g `O` Limit j d ~> Limit j (g `O` d)
-- rightAdjointPreservesLimitsInv = limitUniv @vk @j @k' @(g `O` d) _
-- (\((g :.: lim) :.: j) -> g :.: limit (lim :.: j))

-- | weighted colimits
type HasColimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk a i -> s -> Constraint
class (Equipment hk vk, Ob j) => HasColimits vk (j :: hk a i) k where
  type Colimit (j :: hk a i) (d :: vk i k) :: vk a k
  colimit :: (Ob (d :: vk i k)) => j `O` Conjoint hk vk (Colimit j d) ~> Conjoint hk vk d
  colimitUniv :: (Ob (d :: vk i k), Ob p) => (j `O` Conjoint hk vk p ~> Conjoint hk vk d) -> Colimit j d ~> p