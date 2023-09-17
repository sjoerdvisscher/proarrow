{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)

import Proarrow.Core (PRO, Category(..), type (~>))
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Object (Obj, obj)

type TENSOR k = PRO k (k, k)
type Tensor :: forall {k}. TENSOR k -> Constraint
class (Representable t, Ob @k (U t)) => Tensor (t :: PRO k (k, k)) where
  type U t :: k
  leftUnitor :: Ob a => t % '(U t, a) ~> a
  leftUnitorInv :: Ob a => a ~> t % '(U t, a)
  rightUnitor :: Ob a => t % '(a, U t) ~> a
  rightUnitorInv :: Ob a => a ~> t % '(a, U t)
  associator' :: Obj a -> Obj b -> Obj c -> t % '(t % '(a, b), c) ~> t % '(a, t % '(b, c))
  associatorInv' :: Obj a -> Obj b -> Obj c -> t % '(a, t % '(b, c)) ~> t % '(t % '(a, b), c)

associator
  :: forall {k} t a b c. (Ob (a :: k), Ob b, Ob c, Tensor (t :: PRO k (k, k)))
  => t % '(t % '(a, b), c) ~> t % '(a, t % '(b, c))
associator = associator' @t (obj @a) (obj @b) (obj @c)

associatorInv
  :: forall {k} t a b c. (Ob (a :: k), Ob b, Ob c, Tensor (t :: PRO k (k, k)))
  => t % '(a, t % '(b, c)) ~> t % '(t % '(a, b), c)
associatorInv = associatorInv' @t (obj @a) (obj @b) (obj @c)
