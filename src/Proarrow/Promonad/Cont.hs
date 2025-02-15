module Proarrow.Promonad.Cont where

import Data.Kind (Type)

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Monoidal.Action (Strong (..))
import Proarrow.Core (Profunctor (..), Promonad (..))
import Proarrow.Object.Dual (ExpSA, StarAutonomous (..), currySA, expSA, uncurrySA)
import Proarrow.Object.Exponential (Closed (..), curry, uncurry)

newtype Cont r a b = Cont {runCont :: (b -> r) -> (a -> r)}
instance Profunctor (Cont r) where
  dimap l r (Cont f) = Cont ((. l) . f . (. r))
  r \\ _ = r
instance Promonad (Cont r) where
  id = Cont id
  Cont f . Cont g = Cont (g . f)
instance Strong Type (Cont r) where
  act ab (Cont yrxy) = Cont \byr -> uncurry (yrxy . curry byr . ab)
instance StarAutonomous (KLEISLI (Cont r)) where
  type Dual @(KLEISLI (Cont r)) (KL a) = KL (a -> r)
  dual (Kleisli (Cont f)) = Kleisli (Cont \k br -> k (f br))
  dualInv (Kleisli (Cont f)) = Kleisli (Cont \k b -> f (\g -> g b) k)
  linDist (Kleisli (Cont f)) = Kleisli (Cont \k a -> k (\(b, c) -> f (\g -> g c) (a, b)))
  linDistInv (Kleisli (Cont f)) = Kleisli (Cont \k (a, b) -> k (\c -> f (\g -> g (b, c)) a))
instance Closed (KLEISLI (Cont r)) where
  type a ~~> b = ExpSA a b
  curry' Kleisli{} Kleisli{} = currySA
  uncurry' Kleisli{} Kleisli{} = uncurrySA
  (^^^) = expSA
