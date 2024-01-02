module Proarrow.Category.Monoidal.Rev where

import Proarrow.Core (Profunctor(..))
import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (TENSOR, Tensor(..))
import Proarrow.Profunctor.Representable (Representable (..))

type Rev :: TENSOR k -> TENSOR k
data Rev t a b where
  Rev :: t a '(c, b) -> Rev t a '(b, c)

instance Profunctor t => Profunctor (Rev t) where
  dimap l (r1 :**: r2) (Rev t) = Rev (dimap l (r2 :**: r1) t)
  r \\ Rev t = r \\ t

instance Representable t => Representable (Rev t) where
  type Rev t % '(b, c) = t % '(c, b)
  index (Rev t) = index t
  tabulate f = Rev (tabulate f)
  repMap (f1 :**: f2) = repMap @t (f2 :**: f1)

instance Tensor t => Tensor (Rev t) where
  type U (Rev t) = U t
  leftUnitor = rightUnitor @t
  leftUnitorInv = rightUnitorInv @t
  rightUnitor = leftUnitor @t
  rightUnitorInv = leftUnitorInv @t
  associator a b c = associatorInv @t c b a
  associatorInv a b c = associator @t c b a