module Proarrow.Promonad.Cont where

import Data.Kind (Type)
import Prelude (($))

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Action (Strong (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Object.Dual (ExpSA, StarAutonomous (..), applySA, currySA, expSA)
import Proarrow.Object.Exponential (Closed (..), curry, uncurry)
import Proarrow.Object.BinaryCoproduct (Coprod (..), HasBinaryCoproducts (..), HasCoproducts)

data Cont r a b where
  Cont :: (Ob a, Ob b) => {runCont :: (b ~> r) -> (a ~> r)} -> Cont r a b
instance CategoryOf k => Profunctor (Cont (r :: k)) where
  dimap l r (Cont f) = Cont ((. l) . f . (. r)) \\ l \\ r
  r \\ Cont{} = r
instance CategoryOf k => Promonad (Cont (r :: k)) where
  id = Cont id
  Cont f . Cont g = Cont (g . f)
instance Strong Type (Cont (r :: Type)) where
  act ab (Cont yrxy) = Cont \byr -> uncurry (yrxy . curry byr . ab)

-- | Only premonoidal not monoidal?
instance MonoidalProfunctor (Cont (r :: Type)) where
  par0 = Cont id
  Cont f `par` Cont g = Cont \k (x1, y1) -> f (\x2 -> g (\y2 -> k (x2, y2)) y1) x1

instance HasCoproducts k => MonoidalProfunctor (Coprod (Cont (r :: k))) where
  par0 = Coprod (Cont id)
  Coprod (Cont @af @bf f) `par` Coprod (Cont @ag @bg g) = withObCoprod @k @af @ag $ withObCoprod @k @bf @bg $
    Coprod (Cont (\k -> f (k . lft @_ @bf @bg) ||| g (k . rgt @_ @bf @bg)))

instance StarAutonomous (KLEISLI (Cont (r :: Type))) where
  type Dual @(KLEISLI (Cont r)) (KL a) = KL (a ~~> r)
  dual (Kleisli (Cont f)) = Kleisli (Cont \k br -> k (f br))
  dualInv (Kleisli (Cont f)) = Kleisli (Cont \k b -> f (\g -> g b) k)
  linDist (Kleisli (Cont f)) = Kleisli (Cont \k a -> k (\(b, c) -> f (\g -> g c) (a, b)))
  linDistInv (Kleisli (Cont f)) = Kleisli (Cont \k (a, b) -> k (\c -> f (\g -> g (b, c)) a))
instance Closed (KLEISLI (Cont (r :: Type))) where
  type a ~~> b = ExpSA a b
  withObExp r = r
  curry = currySA
  apply = applySA
  (^^^) = expSA
