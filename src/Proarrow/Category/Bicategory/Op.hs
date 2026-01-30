{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Bicategory.Op where

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..), Bimodule (..), Comonad (..), Monad (..))
import Proarrow.Category.Bicategory.Kan
  ( LeftKanExtension (..)
  , LeftKanLift (..)
  , RightKanExtension (..)
  , RightKanLift (..)
  )
import Proarrow.Category.Equipment (Cotight, CotightAdjoint, Equipment (..), IsOb, Tight, TightAdjoint, WithObO2 (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type OPK :: CAT k -> CAT k
newtype OPK kk j k = OP (kk k j)
type instance UN OP (OP k) = k

type Op :: CAT (OPK kk k j)
data Op a b where
  Op :: a ~> b -> Op (OP a) (OP b)

instance (CategoryOf (kk k j)) => Profunctor (Op :: CAT (OPK kk j k)) where
  dimap = dimapDefault
  r \\ Op f = r \\ f
instance (CategoryOf (kk k j)) => Promonad (Op :: CAT (OPK kk j k)) where
  id = Op id
  Op f . Op g = Op (f . g)
instance (CategoryOf (kk k j)) => CategoryOf (OPK kk j k) where
  type (~>) = Op
  type Ob a = (Is OP a, Ob (UN OP a))

-- | Create a dual of a bicategory by reversing the 1-cells.
instance (Bicategory kk) => Bicategory (OPK kk) where
  type Ob0 (OPK kk) k = Ob0 kk k
  type I = OP I
  type O a b = OP (UN OP b `O` UN OP a)
  withOb2 @(OP a) @(OP b) r = withOb2 @kk @b @a r
  withOb0s @(OP a) r = withOb0s @kk @a r
  r \\\ Op f = r \\\ f
  Op f `o` Op g = Op (g `o` f)
  leftUnitor = Op rightUnitor
  leftUnitorInv = Op rightUnitorInv
  rightUnitor = Op leftUnitor
  rightUnitorInv = Op leftUnitorInv
  associator @(OP p) @(OP q) @(OP r) = Op (associatorInv @kk @r @q @p)
  associatorInv @(OP p) @(OP q) @(OP r) = Op (associator @kk @r @q @p)

type instance IsOb Tight p = IsOb Cotight (UN OP p)
type instance IsOb Cotight p = IsOb Tight (UN OP p)
type instance TightAdjoint p = OP (CotightAdjoint (UN OP p))
type instance CotightAdjoint p = OP (TightAdjoint (UN OP p))
instance (WithObO2 Cotight kk) => WithObO2 Tight (OPK kk) where
  withObO2 @p @q r = withObO2 @Cotight @kk @(UN OP q) @(UN OP p) r
instance (WithObO2 Tight kk) => WithObO2 Cotight (OPK kk) where
  withObO2 @p @q r = withObO2 @Tight @kk @(UN OP q) @(UN OP p) r
instance (Equipment kk) => Equipment (OPK kk) where
  withTightAdjoint @(OP f) r = withCotightAdjoint @kk @f r
  withCotightAdjoint @(OP f) r = withTightAdjoint @kk @f r


-- instance (Equipment hk vk) => HasCompanions (OPK hk) (COK vk) where
--   type Companion (OPK hk) f = OP (Conjoint hk (UN CO f))
--   mapCompanion (Co f) = Op (mapConjoint f)
--   withObCompanion @(CO f) r = withObConjoint @hk @vk @f r
--   compToId = Op conjToId
--   compFromId = Op conjFromId
--   compToCompose (Co f) (Co g) = Op (conjToCompose f g)
--   compFromCompose (Co f) (Co g) = Op (conjFromCompose f g)

-- instance (Equipment hk vk) => Equipment (OPK hk) (COK vk) where
--   type Conjoint (OPK hk) f = OP (Companion hk (UN CO f))
--   mapConjoint (Co f) = Op (mapCompanion f)
--   withObConjoint @(CO f) r = withObCompanion @hk @vk @f r
--   conjToId = Op compToId
--   conjFromId = Op compFromId
--   conjToCompose (Co f) (Co g) = Op (compToCompose f g)
--   conjFromCompose (Co f) (Co g) = Op (compFromCompose f g)
--   comConUnit (Co f) = Op (comConUnit f)
--   comConCounit (Co f) = Op (comConCounit f)

-- instance (Equipment hk vk) => HasCompanions (COK hk) (OPK vk) where
--   type Companion (COK hk) f = CO (Conjoint hk (UN OP f))
--   mapCompanion (Op f) = Co (mapConjoint f)
--   withObCompanion @(OP f) r = withObConjoint @hk @vk @f r
--   compToId = Co conjFromId
--   compFromId = Co conjToId
--   compToCompose (Op f) (Op g) = Co (conjFromCompose g f)
--   compFromCompose (Op f) (Op g) = Co (conjToCompose g f)

-- instance (Equipment hk vk) => Equipment (COK hk) (OPK vk) where
--   type Conjoint (COK hk) f = CO (Companion hk (UN OP f))
--   mapConjoint (Op f) = Co (mapCompanion f)
--   withObConjoint @(OP f) r = withObCompanion @hk @vk @f r
--   conjToId = Co compFromId
--   conjFromId = Co compToId
--   conjToCompose (Op f) (Op g) = Co (compFromCompose g f)
--   conjFromCompose (Op f) (Op g) = Co (compToCompose g f)
--   comConUnit (Op f) = Co (comConCounit f)
--   comConCounit (Op f) = Co (comConUnit f)

-- flipSq :: Sq '(CO p, OP f) '(CO q, OP g) -> Sq '(OP q, CO g) '(OP p, CO f)
-- flipSq (Sq (Co sq)) = Sq (Op sq)

-- flipRetroSq :: RetroSq '(CO p, OP f) '(CO q, OP g) -> RetroSq '(OP q, CO g) '(OP p, CO f)
-- flipRetroSq (RetroSq (Co sq)) = RetroSq (Op sq)

instance (RightKanExtension j f) => RightKanLift (OP j) (OP f) where
  type Rift (OP j) (OP f) = OP (Ran j f)
  rift = Op (ran @j @f)
  riftUniv (Op n) = Op (ranUniv @j @f n)

instance (LeftKanExtension j f) => LeftKanLift (OP j) (OP f) where
  type Lift (OP j) (OP f) = OP (Lan j f)
  lift = Op (lan @j @f)
  liftUniv (Op n) = Op (lanUniv @j @f n)

instance (RightKanLift j f) => RightKanExtension (OP j) (OP f) where
  type Ran (OP j) (OP f) = OP (Rift j f)
  ran = Op (rift @j @f)
  ranUniv (Op n) = Op (riftUniv @j @f n)

instance (LeftKanLift j f) => LeftKanExtension (OP j) (OP f) where
  type Lan (OP j) (OP f) = OP (Lift j f)
  lan = Op (lift @j @f)
  lanUniv (Op n) = Op (liftUniv @j @f n)

instance (Adjunction f g) => Adjunction (OP g) (OP f) where
  unit = Op (unit @f @g)
  counit = Op (counit @f @g)

instance (Monad t) => Monad (OP t) where
  eta = Op eta
  mu = Op mu

instance (Comonad t) => Comonad (OP t) where
  epsilon = Op epsilon
  delta = Op delta

instance (Bimodule s t p) => Bimodule (OP t) (OP s) (OP p) where
  leftAction = Op (rightAction @s @t @p)
  rightAction = Op (leftAction @s @t @p)
