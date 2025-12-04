module Proarrow.Profunctor.Constant where

import Proarrow.Core (CategoryOf (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))

data family Constant :: k -> j +-> k
instance (CategoryOf j, CategoryOf k, Ob c) => FunctorForRep (Constant c :: j +-> k) where
  type Constant c @ a = c
  fmap _ = id
