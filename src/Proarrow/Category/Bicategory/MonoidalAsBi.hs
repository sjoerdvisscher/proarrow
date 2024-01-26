{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Bicategory.MonoidalAsBi where

import Proarrow.Core (CAT, Promonad(..), CategoryOf(..), Profunctor(..), Is, UN, Kind)
import Proarrow.Monoid (Monoid(..))
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Category.Bicategory (Bicategory (..), Monad(..))


type MonK :: Kind -> CAT ()
newtype MonK k i j = MK k
type instance UN MK (MK k) = k

type Mon2 :: forall {k} {i} {j}. CAT (MonK k i j)
data Mon2 a b where
  Mon2 :: a ~> b -> Mon2 (MK a) (MK b)
  deriving (Profunctor, Promonad) via (~>)

instance CategoryOf k => CategoryOf (MonK k i j) where
  type (~>) = Mon2
  type Ob a = (Is MK a, Ob (UN MK a))

instance M.Monoidal k => Bicategory (MonK k) where
  type I = MK M.Unit
  type MK a `O` MK b = MK (a M.** b)
  Mon2 f `o` Mon2 g = Mon2 (f `M.par` g)
  r \\\ Mon2 f = r \\ f
  leftUnitor (Mon2 p) = Mon2 (M.leftUnitor p)
  leftUnitorInv (Mon2 p) = Mon2 (M.leftUnitorInv p)
  rightUnitor (Mon2 p) = Mon2 (M.rightUnitor p)
  rightUnitorInv (Mon2 p) = Mon2 (M.rightUnitorInv p)
  associator (Mon2 p) (Mon2 q) (Mon2 r) = Mon2 (M.associator p q r)
  associatorInv (Mon2 p) (Mon2 q) (Mon2 r) = Mon2 (M.associatorInv p q r)

instance Monoid m => Monad (MK m) where
  eta = Mon2 mempty
  mu = Mon2 mappend