module Proarrow.Category.Instance.Discrete where

import Prelude (type (~))

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, dimapDefault)
import Proarrow.Preorder.ThinCategory qualified as Thin

newtype DISCRETE k = D k
type instance UN D (D a) = a

type Discrete :: CAT (DISCRETE k)
data Discrete a b where
  Refl :: Discrete a a

-- | The discrete category with only identity arrows, every type of kind @k@ is an object.
instance CategoryOf (DISCRETE k) where
  type (~>) = Discrete
instance Profunctor Discrete where
  dimap = dimapDefault
instance Promonad Discrete where
  id = Refl
  Refl . Refl = Refl

instance Thin.ThinProfunctor Discrete where
  type HasArrow Discrete a b = (a ~ b)
  arr = Refl
  withArr Refl r = r

instance Thin.Discrete Discrete where
  withEq Refl r = r

instance DaggerProfunctor Discrete where
  dagger Refl = Refl

newtype CODISCRETE k = CD k
type instance UN CD (CD a) = a

type Codiscrete :: CAT (CODISCRETE k)
data Codiscrete a b where
  Arr :: Codiscrete a b

-- | The codiscrete category has exactly one arrow between every object, every type of kind @k@ is an object.
instance CategoryOf (CODISCRETE k) where
  type (~>) = Codiscrete
instance Profunctor Codiscrete where
  dimap = dimapDefault
instance Promonad Codiscrete where
  id = Arr
  Arr . Arr = Arr

instance Thin.ThinProfunctor Codiscrete where
  type HasArrow Codiscrete a b = ()
  arr = Arr
  withArr Arr r = r

instance Thin.Codiscrete Codiscrete where
  anyArr = Arr

instance DaggerProfunctor Codiscrete where
  dagger Arr = Arr