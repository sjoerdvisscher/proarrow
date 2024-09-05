{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Preorder.Constraint where

import Data.Kind (Constraint)

import Proarrow.Preorder (CProfunctor (..), CPromonad (..), Dict (..), POS, PreorderOf (..), type (:-) (..))

class ((a) => b) => a :=> b where
  entails :: a :- b
instance ((a) => b) => a :=> b where
  entails = Sub Dict

instance CProfunctor ((:=>) :: POS Constraint) where
  cdimap = Sub Dict
  obs = Sub Dict
instance CPromonad ((:=>) :: POS Constraint) where
  cid = Sub Dict
  ccomp = Sub Dict
instance PreorderOf Constraint where
  type (<=) = (:=>)
