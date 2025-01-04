{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Equipment.Limit where

import Data.Kind (Constraint)

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Equipment (HasCompanions (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj)

-- | weighted limits
type HasLimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk i a -> s -> Constraint
class (HasCompanions hk vk, Ob j) => HasLimits vk (j :: hk i a) k where
  type Limit (j :: hk i a) (d :: vk i k) :: vk a k
  limitObj :: Ob (d :: vk i k) => Obj (Limit j d)
  limit :: (Ob (d :: vk i k)) => Companion hk (Limit j d) `O` j ~> Companion hk d
  limitUniv :: (Ob (d :: vk i k), Ob p) => Companion hk p `O` j ~> Companion hk d -> p ~> Limit j d

-- | weighted colimits
type HasColimits :: forall {s} {hk :: CAT s} {a :: s} {i :: s}. CAT s -> hk a i -> s -> Constraint
class (HasCompanions hk vk, Ob j) => HasColimits vk (j :: hk a i) k where
  type Colimit (j :: hk a i) (d :: vk i k) :: vk a k
  colimitObj :: Ob (d :: vk i k) => Obj (Colimit j d)
  colimit :: (Ob (d :: vk i k)) => Companion hk d `O` j ~> Companion hk (Colimit j d)
  colimitUniv :: (Ob (d :: vk i k), Ob p) => Companion hk d `O` j ~> Companion hk p -> Colimit j d ~> p
