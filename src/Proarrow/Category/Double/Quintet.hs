module Proarrow.Category.Double.Quintet where

import Proarrow.Category.Bicategory (Bicategory (..))
import Proarrow.Category.Bicategory.Co (COK (..), Co (..))
import Proarrow.Category.Double (HasCompanions (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type data QKK kk i j = QK (kk i j)
type instance UN QK (QK p) = p

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
  r \\\ Q2 f = r \\\ f
  Q2 f `o` Q2 g = Q2 (f `o` g)
  leftUnitor (Q2 p) = Q2 (leftUnitor p)
  leftUnitorInv (Q2 p) = Q2 (leftUnitorInv p)
  rightUnitor (Q2 p) = Q2 (rightUnitor p)
  rightUnitorInv (Q2 p) = Q2 (rightUnitorInv p)
  associator (Q2 p) (Q2 q) (Q2 r) = Q2 (associator p q r)
  associatorInv (Q2 p) (Q2 q) (Q2 r) = Q2 (associatorInv p q r)

instance (Bicategory kk) => HasCompanions (QKK kk) (COK kk) where
  type Companion (QKK kk) (COK kk) f = QK (UN CO f)
  mapCompanion (Co f) = Q2 f
  compToId = Q2 id
  compFromId = Q2 id
  compToCompose (Co f) (Co g) = Q2 (f `o` g)
  compFromCompose (Co f) (Co g) = Q2 (f `o` g)
