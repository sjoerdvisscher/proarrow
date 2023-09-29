module Proarrow.Promonad.State where

import Prelude (fmap)

import Proarrow.Promonad (Promonad(..))
import Proarrow.Core (Category(..), Profunctor(..))


newtype State s a b = State { getState :: (s, a) -> (s, b) }

instance Profunctor (State s) where
  dimap l r (State f) = State (fmap r . f . fmap l)

instance Promonad (State s) where
  unit = State id
  mult (State f) (State g) = State (g . f)
