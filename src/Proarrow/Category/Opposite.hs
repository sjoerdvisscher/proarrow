module Proarrow.Category.Opposite where

import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..), Thin)
import Proarrow.Core (CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, lmap, type (+->))
import Proarrow.Functor (Functor (..))

newtype OPPOSITE k = OP k
type instance UN OP (OP k) = k

type Op :: j +-> k -> OPPOSITE k +-> OPPOSITE j
data Op p a b where
  Op :: {unOp :: p b a} -> Op p (OP a) (OP b)

instance (Profunctor p) => Functor (Op p a) where
  map (Op f) (Op p) = Op (lmap f p)

instance (Profunctor p) => Profunctor (Op p) where
  dimap (Op l) (Op r) = Op . dimap r l . unOp
  r \\ Op f = r \\ f

-- | The opposite category of the category of `k`.
instance (CategoryOf k) => CategoryOf (OPPOSITE k) where
  type (~>) = Op (~>)
  type Ob a = (Is OP a, Ob (UN OP a))

instance (Promonad c) => Promonad (Op c) where
  id = Op id
  Op f . Op g = Op (g . f)

instance (ThinProfunctor p) => ThinProfunctor (Op p) where
  type HasArrow (Op p) (OP a) (OP b) = HasArrow p b a
  arr = Op arr
  withArr (Op f) r = withArr f r

type UnOp :: OPPOSITE k +-> OPPOSITE j -> j +-> k
data UnOp p a b where
  UnOp :: {unUnOp :: p (OP b) (OP a)} -> UnOp p a b
instance (CategoryOf j, CategoryOf k, Profunctor p) => Profunctor (UnOp p :: j +-> k) where
  dimap l r = UnOp . dimap (Op r) (Op l) . unUnOp
  r \\ UnOp f = r \\ f

instance (Thin j, Thin k, ThinProfunctor p) => ThinProfunctor (UnOp p :: j +-> k) where
  type HasArrow (UnOp p) a b = HasArrow p (OP b) (OP a)
  arr = unOp arr
  withArr f r = withArr (Op f) r

