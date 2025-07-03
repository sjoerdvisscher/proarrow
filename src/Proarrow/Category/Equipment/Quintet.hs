module Proarrow.Category.Equipment.Quintet where

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.MonoidalAsBi (Mon2 (..), MonK (..))
import Proarrow.Category.Equipment (HasCompanions (..), Sq (..), vArr)
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type data QKK kk i j = QK (kk i j)
type instance UN QK (QK p) = p

type QuintetSq (f :: kk a b) (g :: kk a c) (h :: kk b d) (k :: kk c d) = Sq '(QK f, h) '(QK k, g)

type Q2 :: CAT (QKK kk i j)
data Q2 a b where
  Q2 :: a ~> b -> Q2 (QK a) (QK b)
instance (CategoryOf (kk i j)) => Profunctor (Q2 :: CAT (QKK kk i j)) where
  dimap = dimapDefault
  r \\ Q2 p = r \\ p
instance (CategoryOf (kk i j)) => Promonad (Q2 :: CAT (QKK kk i j)) where
  id = Q2 id
  Q2 f . Q2 g = Q2 (f . g)
instance (CategoryOf (kk i j)) => CategoryOf (QKK kk i j) where
  type (~>) = Q2
  type Ob (a :: QKK kk i j) = (Is QK a, Ob (UN QK a))

instance (Bicategory kk) => Bicategory (QKK kk) where
  type Ob0 (QKK kk) k = Ob0 kk k
  type I = QK I
  type O a b = QK (UN QK a `O` UN QK b)
  withOb2 @(QK a) @(QK b) = withOb2 @kk @a @b
  withOb0s @(QK a) = withOb0s @kk @a
  r \\\ Q2 f = r \\\ f
  Q2 f `o` Q2 g = Q2 (f `o` g)
  leftUnitor = Q2 leftUnitor
  leftUnitorInv = Q2 leftUnitorInv
  rightUnitor = Q2 rightUnitor
  rightUnitorInv = Q2 rightUnitorInv
  associator @(QK p) @(QK q) @(QK r) = Q2 (associator @kk @p @q @r)
  associatorInv @(QK p) @(QK q) @(QK r) = Q2 (associatorInv @kk @p @q @r)

instance (Bicategory kk) => HasCompanions (QKK kk) kk where
  type Companion (QKK kk) f = QK f
  mapCompanion f = Q2 f
  withObCompanion r = r
  compToId = Q2 id
  compFromId = Q2 id
  compToCompose f g = Q2 (f `o` g)
  compFromCompose f g = Q2 (f `o` g)

-- | BiPara as a quintet construction.
type BiParaSq (a :: k) b p q = QuintetSq (MK p :: MonK k '() '()) (MK b) (MK a) (MK q :: MonK k '() '())

bipara :: (Ob p, Ob q, Ob a, Ob b) => a M.** p ~> q M.** b -> BiParaSq a b p q
bipara n = Sq (Q2 (Mon2 n))

reparam :: forall {k} (a :: k) (b :: k). (M.Monoidal k) => a ~> b -> BiParaSq a b M.Unit M.Unit
reparam f = vArr (Mon2 f)