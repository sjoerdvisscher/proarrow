module Proarrow.Category.Bicategory.Bidiscrete where

import Data.Type.Equality (type (~), type (~~))

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Core (CAT, CategoryOf (..), OB, Profunctor (..), Promonad (..), dimapDefault)

type DiscreteK :: forall {c}. OB c -> CAT c
type data DiscreteK (ob :: OB c) j k where
  DK :: DiscreteK ob j j
type Bidiscrete :: CAT (DiscreteK ob j k)
data Bidiscrete a b where
  Bidiscrete :: (ob j) => Bidiscrete (DK :: DiscreteK ob j j) DK

instance Profunctor Bidiscrete where
  dimap = dimapDefault
  r \\ Bidiscrete = r
instance Promonad Bidiscrete where
  id = Bidiscrete
  Bidiscrete . Bidiscrete = Bidiscrete
instance CategoryOf (DiscreteK ob j k) where
  type (~>) = Bidiscrete
  type Ob (a :: DiscreteK ob j k) = (j ~ k, a ~~ (DK :: DiscreteK ob j j), ob j)

-- | The bicategory with only identity 1-cells and identity 2-cells between those.
instance CategoryOf c => Bicategory (DiscreteK (ob :: OB c)) where
  type Ob0 (DiscreteK ob) k = ob k
  type I = DK
  type DK `O` DK = DK
  withOb2 r = r
  Bidiscrete `o` Bidiscrete = Bidiscrete
  r \\\ Bidiscrete = r
  leftUnitor = Bidiscrete
  leftUnitorInv = Bidiscrete
  rightUnitor = Bidiscrete
  rightUnitorInv = Bidiscrete
  associator = Bidiscrete
  associatorInv = Bidiscrete
