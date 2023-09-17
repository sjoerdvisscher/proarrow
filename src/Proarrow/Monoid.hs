{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Monoid where

import Data.Kind (Constraint)
import Prelude qualified as P

import Proarrow.Core (type (~>))
import Proarrow.Category.Monoidal (Tensor(..), TENSOR)
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Object.BinaryProduct (ProductFunctor)

-- The types for `unit` and `mult` are so ambiguous that they are not really useable.
-- Instead this is a way for more speciallized classes to show that they express a kind of Monoid.
class (Tensor (Ten c :: TENSOR k)) => Monoid (c :: Constraint) (m :: k) where
  type Ten c :: TENSOR k
  unit :: c => U (Ten c) ~> m
  mult :: c => Ten c % '(m, m) ~> m

instance Monoid (P.Monoid m) m where
  type Ten (P.Monoid m) = ProductFunctor
  unit () = P.mempty
  mult (m, n) = m P.<> n