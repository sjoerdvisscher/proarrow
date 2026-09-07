{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Coclosed monoidal categories, dual to "Proarrow.Category.Monoidal.Closed": 'Coclosed' provides
-- the coexponential @a '<~~' b@, left adjoint to tensoring, with 'coeval' and its universal property
-- 'coevalUniv'; 'CoCCC' is the cocartesian coclosed case.
module Proarrow.Category.Monoidal.Coclosed where

import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Colimit.BinaryCoproduct (Cocartesian)
import Proarrow.Core (CategoryOf (..))

class (Monoidal k) => Coclosed k where
  type (a :: k) <~~ (b :: k) :: k
  withObCoExp :: (Ob (a :: k), Ob b) => ((Ob (a <~~ b)) => r) -> r
  coeval :: (Ob (a :: k), Ob b) => a ~> (a <~~ b) ** b
  coevalUniv :: (Ob (b :: k), Ob c) => a ~> c ** b -> (a <~~ b) ~> c

instance Coclosed () where
  type (a :: ()) <~~ (b :: ()) = '()
  withObCoExp f = f
  coeval = Unit
  coevalUniv Unit = Unit

class (Cocartesian k, Coclosed k) => CoCCC k
instance (Cocartesian k, Coclosed k) => CoCCC k
