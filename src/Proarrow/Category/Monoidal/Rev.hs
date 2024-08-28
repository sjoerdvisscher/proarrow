module Proarrow.Category.Monoidal.Rev where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type data REV k = R k
type instance UN R (R a) = a

type Rev :: CAT k
data Rev a b where
  Rev :: a ~> b -> Rev (R a) (R b)

instance (CategoryOf k) => Profunctor (Rev :: CAT (REV k)) where
  dimap = dimapDefault
  r \\ Rev t = r \\ t

instance (CategoryOf k) => Promonad (Rev :: CAT (REV k)) where
  id = Rev id
  Rev f . Rev g = Rev (f . g)

instance (CategoryOf k) => CategoryOf (REV k) where
  type (~>) = Rev
  type Ob a = (Is R a, Ob (UN R a))

instance (Monoidal k) => MonoidalProfunctor (Rev :: CAT (REV k)) where
  par0 = Rev par0
  Rev f `par` Rev g = Rev (g `par` f)

instance (Monoidal k) => Monoidal (REV k) where
  type Unit = R Unit
  type (R a) ** (R b) = R (b ** a)
  leftUnitor (Rev a) = Rev (rightUnitor a)
  leftUnitorInv (Rev a) = Rev (rightUnitorInv a)
  rightUnitor (Rev a) = Rev (leftUnitor a)
  rightUnitorInv (Rev a) = Rev (leftUnitorInv a)
  associator (Rev a) (Rev b) (Rev c) = Rev (associatorInv c b a)
  associatorInv (Rev a) (Rev b) (Rev c) = Rev (associator c b a)

instance (SymMonoidal k) => SymMonoidal (REV k) where
  swap' (Rev a) (Rev b) = Rev (swap' b a)
