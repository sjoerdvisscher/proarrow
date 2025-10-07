{-# LANGUAGE DerivingStrategies #-}

module Proarrow.Profunctor.Ran where

import Prelude (type (~))

import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Limit (HasLimits (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Profunctor.Star (Star (..))

-- Note: Ran and Rift are swapped compared to the profunctors package.

type j |> p = Ran (OP j) p

type Ran :: OPPOSITE (i +-> j) -> i +-> k -> j +-> k
data Ran j p a b where
  Ran :: (Ob a, Ob b) => {unRan :: forall x. j b x -> p a x} -> Ran (OP j) p a b

runRan :: (Profunctor j) => j b x -> Ran (OP j) p a b -> p a x
runRan j (Ran k) = k j \\ j

flipRan :: (Functor j, Profunctor p) => Costar j |> p ~> p :.: Star j
flipRan = Prof \(Ran k) -> k (Costar id) :.: Star id

flipRanInv :: (Functor j, Profunctor p) => p :.: Star j ~> Costar j |> p
flipRanInv = Prof \(p :.: Star f) -> p // Ran \(Costar g) -> rmap (g . f) p

instance (Profunctor p, Profunctor j) => Profunctor (Ran (OP j) p) where
  dimap l r (Ran k) = l // r // Ran (lmap l . k . lmap r)
  r \\ Ran{} = r

instance (Profunctor j) => Functor (Ran (OP j)) where
  map (Prof n) = Prof \(Ran k) -> Ran (n . k)

instance Functor Ran where
  map (Op (Prof n)) = Nat (Prof \(Ran k) -> Ran (k . n))

instance (p ~ j, Profunctor p) => Promonad (Ran (OP j) p) where
  id = Ran id
  Ran l . Ran r = Ran (r . l)

instance (HasLimits j k, Representable d) => Representable (Ran (OP j) (d :: i +-> k)) where
  type Ran (OP j) d % a = Limit j d % a
  index = index @(Limit j d) . limitUniv @j @k @d (\(Ran k' :.: j) -> k' j)
  tabulate f = Ran (\j -> limit (tabulate f :.: j)) \\ f
  repMap = repMap @(Limit j d)

type PWRan j p a = (j |> p) % a

-- a ~> PWRan j p b = forall x. (b ~> j x) -> a ~> p x
-- a ~> PWRan j p b = forall x. a ~> (p x ^ (b ~> j x))
-- PWRan j p b = forall x. p x ^ (b ~> j x)
class (Representable p, Representable j, Representable (j |> p)) => PointwiseRightKanExtension j p
instance (Representable p, Representable j, Representable (j |> p)) => PointwiseRightKanExtension j p

type PWLift j p a = (j |> p) %% a

-- PWLift j p a ~> b = forall x. (j b ~> x) -> p a ~> x
-- PWLift j p a ~> b = p a ~> j b
class (Corepresentable j, Corepresentable p, Corepresentable (j |> p)) => PointwiseLeftKanLift j p
instance (Corepresentable j, Corepresentable p, Corepresentable (j |> p)) => PointwiseLeftKanLift j p

instance (Profunctor j) => Corepresentable (Star (Ran (OP j))) where
  type Star (Ran (OP j)) %% p = p :.: j
  coindex (Star (Prof f)) = Prof \(p :.: j) -> runRan j (f p)
  cotabulate (Prof f) = Star (Prof \p -> p // Ran \q -> f (p :.: q))
  corepMap (Prof f) = Prof \(p :.: j) -> f p :.: j

ranCompose :: (Profunctor i, Profunctor j, Profunctor p) => i |> (j |> p) ~> (i :.: j) |> p
ranCompose = Prof \k -> k // Ran \(i :.: j) -> runRan j (runRan i k)

ranComposeInv :: (Profunctor i, Profunctor j, Profunctor p) => (i :.: j) |> p ~> i |> (j |> p)
ranComposeInv = Prof \k -> k // Ran \i -> i // Ran \j -> runRan (i :.: j) k

ranHom :: (Profunctor p) => p ~> (~>) |> p
ranHom = Prof \p -> p // Ran \j -> rmap j p

ranHomInv :: (Profunctor p) => (~>) |> p ~> p
ranHomInv = Prof \(Ran k) -> k id