{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Preorder where

import Data.Kind (Constraint)
import Prelude (type (~))

infixl 1 \\

type POS k = k -> k -> Constraint

data Dict a where
  Dict :: (a) => Dict a
newtype a :- b = Sub ((a) => Dict b)

(\\) :: (a) => ((c) => r) -> (a :- c) -> r
r \\ Sub Dict = r

class (CPromonad ((<=) :: POS k)) => PreorderOf k where
  type (<=) :: POS k
  type COb (a :: k) :: Constraint
  type COb a = ()

type IsPosetOf k pos = (PreorderOf k, pos ~ (<=) @k, CPromonad pos)

class CProfunctor p where
  cdimap :: (c <= a, b <= d, p a b) :- p c d
  obs :: p a b :- (COb a, COb b)
class CProfunctor p => CPromonad p where
  cid :: (COb a) => () :- p a a
  ccomp :: forall a b c. (p b c, p a b) :- p a c

cdimapDefault :: forall p a b c d. (CPromonad p) => (p c a, p b d, p a b) :- p c d
cdimapDefault = Sub (Dict \\ ccomp @p @c @b @d \\ ccomp @p @c @a @b)
