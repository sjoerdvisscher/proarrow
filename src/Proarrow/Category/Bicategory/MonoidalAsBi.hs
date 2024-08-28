module Proarrow.Category.Bicategory.MonoidalAsBi where

import Proarrow.Category.Bicategory (Bicategory (..), Comonad (..), Monad (..))
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CAT, CategoryOf (..), Is, Kind, Profunctor (..), Promonad (..), UN)
import Proarrow.Monoid (Comonoid (..), Monoid (..))

type MonK :: Kind -> CAT ()
newtype MonK k i j = MK k
type instance UN MK (MK k) = k

type Mon2 :: forall {k} {i} {j}. CAT (MonK k i j)
data Mon2 a b where
  Mon2 :: a ~> b -> Mon2 (MK a) (MK b)
  deriving (Profunctor, Promonad) via (~>)

instance (CategoryOf k) => CategoryOf (MonK k i j) where
  type (~>) = Mon2
  type Ob a = (Is MK a, Ob (UN MK a))

-- | A monoidal category as a bicategory.
instance (M.Monoidal k) => Bicategory (MonK k) where
  type I = MK M.Unit
  type MK a `O` MK b = MK (b M.** a)
  iObj = Mon2 M.par0
  Mon2 f `o` Mon2 g = Mon2 (g `M.par` f)
  r \\\ Mon2 f = r \\ f
  leftUnitor (Mon2 p) = Mon2 (M.rightUnitor p)
  leftUnitorInv (Mon2 p) = Mon2 (M.rightUnitorInv p)
  rightUnitor (Mon2 p) = Mon2 (M.leftUnitor p)
  rightUnitorInv (Mon2 p) = Mon2 (M.leftUnitorInv p)
  associator (Mon2 p) (Mon2 q) (Mon2 r) = Mon2 (M.associatorInv r q p)
  associatorInv (Mon2 p) (Mon2 q) (Mon2 r) = Mon2 (M.associator r q p)

-- | Monoids in a monoidal category are monads when the monoidal category is seen as a bicategory.
instance (Monoid m) => Monad (MK m) where
  eta = Mon2 mempty
  mu = Mon2 mappend

-- | Comonoids in a monoidal category are comonads when the monoidal category is seen as a bicategory.
instance (Comonoid m) => Comonad (MK m) where
  epsilon = Mon2 counit
  delta = Mon2 comult
