{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Coclosed monoidal categories, dual to "Proarrow.Category.Monoidal.Closed": 'Coclosed' provides
-- the coexponential @a '<~~' b@, left adjoint to tensoring, with 'coeval' and its universal property
-- 'coevalUniv'; 'CoCCC' is the cocartesian coclosed case.
module Proarrow.Category.Monoidal.Coclosed where

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.Cartesian (Cartesian)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Cocartesian
  , Coprod (..)
  , HasCoproducts
  )
import Proarrow.Core (CategoryOf (..), UN)
import Proarrow.Limit.BinaryProduct (PROD (..), Prod (..))

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

instance (Coclosed k) => Closed (OPPOSITE k) where
  type OP a ~~> OP b = OP (b <~~ a)
  withObExp @(OP a) @(OP b) r = withObCoExp @k @b @a r
  curry @(OP a) @(OP b) (Op f) = Op (coevalUniv @k @b @a f)
  apply @(OP a) @(OP b) = Op (coeval @k @b @a)

instance (Closed k) => Coclosed (OPPOSITE k) where
  type OP a <~~ OP b = OP (b ~~> a)
  withObCoExp @(OP a) @(OP b) r = withObExp @k @b @a r
  coeval @(OP a) @(OP b) = Op (apply @_ @b @a)
  coevalUniv @(OP b) @(OP c) (Op f) = Op (curry @k @c @b f)

instance (HasCoproducts k, Coclosed (COPROD k)) => Closed (PROD (OPPOSITE k)) where
  type PR (OP a) ~~> PR (OP b) = PR (OP (UN COPR (COPR b <~~ COPR a)))
  withObExp @(PR (OP a)) @(PR (OP b)) r = withObCoExp @(COPROD k) @(COPR b) @(COPR a) r
  curry @(PR (OP a)) @(PR (OP b)) (Prod (Op f)) =
    case coevalUniv @(COPROD k) @(COPR b) @(COPR a) (Coprod f) of
      Coprod g -> Prod (Op g)
  apply @(PR (OP a)) @(PR (OP b)) = Prod (Op (unCoprod (coeval @(COPROD k) @(COPR b) @(COPR a))))

instance (Cartesian k, Closed (PROD k)) => Coclosed (COPROD (OPPOSITE k)) where
  type COPR (OP a) <~~ COPR (OP b) = COPR (OP (UN PR (PR b ~~> PR a)))
  withObCoExp @(COPR (OP a)) @(COPR (OP b)) r = withObExp @(PROD k) @(PR b) @(PR a) r
  coeval @(COPR (OP a)) @(COPR (OP b)) = Coprod (Op (unProd (apply @_ @(PR b) @(PR a))))
  coevalUniv @(COPR (OP b)) @(COPR (OP c)) (Coprod (Op f)) =
    case curry @_ @(PR c) @(PR b) (Prod f) of
      Prod g -> Coprod (Op g)

class (Cocartesian k, Coclosed k) => CoCCC k
instance (Cocartesian k, Coclosed k) => CoCCC k
