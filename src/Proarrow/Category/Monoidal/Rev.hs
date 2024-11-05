module Proarrow.Category.Monoidal.Rev where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, type (+->))

type data REV k = R k
type instance UN R (R a) = a

type Rev :: j +-> k -> REV j +-> REV k
data Rev p a b where
  Rev :: p a b -> Rev p (R a) (R b)

instance (Profunctor p) => Profunctor (Rev p) where
  dimap (Rev l) (Rev r) (Rev p) = Rev (dimap l r p)
  r \\ Rev p = r \\ p

instance (Promonad p) => Promonad (Rev p) where
  id = Rev id
  Rev f . Rev g = Rev (f . g)

instance (CategoryOf k) => CategoryOf (REV k) where
  type (~>) = Rev (~>)
  type Ob a = (Is R a, Ob (UN R a))

instance (MonoidalProfunctor p) => MonoidalProfunctor (Rev p) where
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
