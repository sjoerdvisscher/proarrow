{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Bicategory.Op where

import Proarrow.Category.Bicategory (Adjunction (..), Bicategory (..), Bimodule (..), Comonad (..), Monad (..))
import Proarrow.Category.Bicategory.Kan
  ( LeftKanExtension (..)
  , LeftKanLift (..)
  , RightKanExtension (..)
  , RightKanLift (..)
  )
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
  r \\\ Op f = r \\\ f
  iObj = Op iObj
  Op f `o` Op g = Op (g `o` f)
  leftUnitor (Op p) = Op (rightUnitor p)
  leftUnitorInv (Op p) = Op (rightUnitorInv p)
  rightUnitor (Op p) = Op (leftUnitor p)
  rightUnitorInv (Op p) = Op (leftUnitorInv p)
  associator (Op p) (Op q) (Op r) = Op (associatorInv r q p)
  associatorInv (Op p) (Op q) (Op r) = Op (associator r q p)

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
