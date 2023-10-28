module Proarrow.Promonad.State where

import Prelude (fmap)

import Proarrow.Core (Promonad(..), Profunctor(..))


newtype State s a b = State { getState :: (s, a) -> (s, b) }

instance Profunctor (State s) where
  dimap l r (State f) = State (fmap r . f . fmap l)

instance Promonad (State s) where
  id = State id
  State f . State g = State (f . g)
