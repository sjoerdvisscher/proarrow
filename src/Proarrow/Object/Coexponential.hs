{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Coexponential where

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Core (CategoryOf (..), Obj, obj)
import Proarrow.Object.BinaryCoproduct (Cocartesian)

class (Monoidal k) => Coclosed k where
  type (a :: k) <~~ (b :: k) :: k
  coeval' :: Obj (a :: k) -> Obj b -> a ~> (a <~~ b) ** b
  coevalUniv' :: Obj (b :: k) -> Obj c -> a ~> c ** b -> (a <~~ b) ~> c

coeval :: forall {k} (a :: k) b. (Coclosed k, Ob a, Ob b) => a ~> (a <~~ b) ** b
coeval = coeval' (obj @a) (obj @b)

coevalUniv :: forall {k} (a :: k) b c. (Coclosed k, Ob b, Ob c) => a ~> c ** b -> (a <~~ b) ~> c
coevalUniv = coevalUniv' (obj @b) (obj @c)

class (Cocartesian k, Coclosed k) => CoCCC k
instance (Cocartesian k, Coclosed k) => CoCCC k
