module Proarrow.Category.Bicategory.Bidiscrete where

import Data.Type.Equality (type (~), type (~~))

import Proarrow.Category.Bicategory (Bicategory(..))
import Proarrow.Core (CAT, Profunctor (..), Promonad (..), CategoryOf(..), dimapDefault, Kind)

type DiscreteK :: CAT Kind
data DiscreteK j k where
  DK :: DiscreteK j j
type Bidiscrete :: CAT (DiscreteK j k)
data Bidiscrete a b where
  Bidiscrete :: Bidiscrete DK DK

instance Profunctor Bidiscrete where
  dimap = dimapDefault
  r \\ Bidiscrete = r
instance Promonad Bidiscrete where
  id = Bidiscrete
  Bidiscrete . Bidiscrete = Bidiscrete
instance CategoryOf (DiscreteK j k) where
  type (~>) = Bidiscrete
  type Ob (a :: DiscreteK j k) = (j ~ k, a ~~ (DK :: DiscreteK j j))

-- | The bicategory with only identity 1-cells and identity 2-cells between those.
instance Bicategory DiscreteK where
  type I = DK
  type DK `O` DK = DK
  Bidiscrete `o` Bidiscrete = Bidiscrete
  r \\\ Bidiscrete = r
  leftUnitor Bidiscrete = Bidiscrete
  leftUnitorInv Bidiscrete = Bidiscrete
  rightUnitor Bidiscrete = Bidiscrete
  rightUnitorInv Bidiscrete = Bidiscrete
  associator Bidiscrete Bidiscrete Bidiscrete = Bidiscrete
  associatorInv Bidiscrete Bidiscrete Bidiscrete = Bidiscrete