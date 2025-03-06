{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Coexponential where

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CategoryOf (..))
import Proarrow.Object.BinaryCoproduct (Cocartesian)

class (Monoidal k) => Coclosed k where
  type (a :: k) <~~ (b :: k) :: k
  withObCoExp :: (Ob (a :: k), Ob b) => ((Ob (a <~~ b)) => r) -> r
  coeval :: (Ob (a :: k), Ob b) => a ~> (a <~~ b) ** b
  coevalUniv :: (Ob (b :: k), Ob c) => a ~> c ** b -> (a <~~ b) ~> c

class (Cocartesian k, Coclosed k) => CoCCC k
instance (Cocartesian k, Coclosed k) => CoCCC k
