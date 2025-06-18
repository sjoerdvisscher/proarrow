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

-- | The reverse of the category of @k@, i.e. with the tensor flipped.
instance (CategoryOf k) => CategoryOf (REV k) where
  type (~>) = Rev (~>)
  type Ob a = (Is R a, Ob (UN R a))

instance (MonoidalProfunctor p) => MonoidalProfunctor (Rev p) where
  par0 = Rev par0
  Rev f `par` Rev g = Rev (g `par` f)

-- | The flipped tensor.
instance (Monoidal k) => Monoidal (REV k) where
  type Unit = R Unit
  type R a ** R b = R (b ** a)
  withOb2 @(R a) @(R b) = withOb2 @k @b @a
  leftUnitor = Rev rightUnitor
  leftUnitorInv = Rev rightUnitorInv
  rightUnitor = Rev leftUnitor
  rightUnitorInv = Rev leftUnitorInv
  associator @(R a) @(R b) @(R c) = Rev (associatorInv @k @c @b @a)
  associatorInv @(R a) @(R b) @(R c) = Rev (associator @k @c @b @a)

instance (SymMonoidal k) => SymMonoidal (REV k) where
  swap @(R a) @(R b) = Rev (swap @k @b @a)
