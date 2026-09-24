{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Coclosed monoidal categories, dual to "Proarrow.Category.Monoidal.Closed": 'Coclosed' provides
-- the coexponential @a '<~~' b@, left adjoint to tensoring, with 'coeval' and its universal property
-- 'coevalUniv'; 'CoCCC' is the cocartesian coclosed case.
module Proarrow.Category.Monoidal.Coclosed where

import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Colimit.BinaryCoproduct (Cocartesian)
import Proarrow.Core (CategoryOf (..))

-- | A coclosed monoidal category, dual to 'Proarrow.Category.Monoidal.Closed.Closed': the
-- coexponential @a '<~~' b@ is /left/ adjoint to tensoring with @b@, so 'coevalUniv' witnesses
-- @Hom(a '<~~' b, c) ≅ Hom(a, c '**' b)@ with 'coeval' as the unit.
--
-- __Laws:__
--
-- * @'coevalUniv'@ is a bijection, inverted by @\\g -> (g '**' 'id') . 'coeval'@:
--   @('coevalUniv' f '**' 'id') . 'coeval' = f@ and @'coevalUniv' ((g '**' 'id') . 'coeval') = g@
-- * and natural in all three variables, dually to 'Proarrow.Category.Monoidal.Closed.curry'.
--
-- Unlike those of 'Proarrow.Category.Monoidal.Closed.Closed', these laws have no check in
-- "Proarrow.Testing.Laws".
class (Monoidal k) => Coclosed k where
  -- | The coexponential object.
  type (a :: k) <~~ (b :: k) :: k

  -- | Recovers @'Ob' (a '<~~' b)@ from the objecthood of the ends.
  withObCoExp :: (Ob (a :: k), Ob b) => ((Ob (a <~~ b)) => r) -> r

  -- | Co-evaluation: the unit of the adjunction.
  coeval :: (Ob (a :: k), Ob b) => a ~> (a <~~ b) ** b

  -- | Transposes an arrow into a tensor into one out of a coexponential.
  coevalUniv :: (Ob (b :: k), Ob c) => a ~> c ** b -> (a <~~ b) ~> c

instance Coclosed () where
  type (a :: ()) <~~ (b :: ()) = '()
  withObCoExp f = f
  coeval = Unit
  coevalUniv Unit = Unit

class (Cocartesian k, Coclosed k) => CoCCC k
instance (Cocartesian k, Coclosed k) => CoCCC k
