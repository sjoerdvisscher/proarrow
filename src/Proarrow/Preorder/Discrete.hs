module Proarrow.Preorder.Discrete where

import Prelude (type (~))

import Proarrow.Preorder (CProfunctor (..), CPromonad (..), Dict (..), POS, PreorderOf (..), type (:-) (..))

newtype DISCRETE k = D k
instance CProfunctor ((~) :: POS (DISCRETE k)) where
  cdimap = Sub Dict
  obs = Sub Dict
instance CPromonad ((~) :: POS (DISCRETE k)) where
  cid = Sub Dict
  ccomp = Sub Dict
instance PreorderOf (DISCRETE k) where
  type (<=) = (~)