module Proarrow.Profunctor.Rift where

import Prelude (type (~))

import Proarrow.Category.Colimit (HasColimits (..))
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Representable (Representable (..))
import Proarrow.Profunctor.Star (Star (..))

-- Note: Ran and Rift are swapped compared to the profunctors package.

type p <| j = Rift (OP j) p

type Rift :: OPPOSITE (k +-> i) -> j +-> i -> j +-> k
data Rift j p a b where
  Rift :: (Ob a, Ob b) => {unRift :: forall x. j x a -> p x b} -> Rift (OP j) p a b

runRift :: (Profunctor j) => j x a -> Rift (OP j) p a b -> p x b
runRift j (Rift k) = k j \\ j

flipRift :: (Functor j, Profunctor p) => p <| Star j ~> Costar j :.: p
flipRift = Prof \(Rift k) -> Costar id :.: k (Star id)

flipRiftInv :: (Functor j, Profunctor p) => Costar j :.: p ~> p <| Star j
flipRiftInv = Prof \(Costar f :.: p) -> p // Rift \(Star g) -> lmap (f . g) p

instance (Profunctor p, Profunctor j) => Profunctor (Rift (OP j) p) where
  dimap l r (Rift k) = r // l // Rift (rmap r . k . rmap l)
  r \\ Rift{} = r

instance (Profunctor j) => Functor (Rift (OP j)) where
  map (Prof n) = Prof \(Rift k) -> Rift (n . k)

instance Functor Rift where
  map (Op (Prof n)) = Nat (Prof \(Rift k) -> Rift (k . n))

instance (Profunctor j) => Corepresentable (Star (Rift (OP j))) where
  type Star (Rift (OP j)) %% p = j :.: p
  coindex (Star (Prof f)) = Prof \(j :.: p) -> runRift j (f p)
  cotabulate (Prof f) = Star (Prof \p -> p // Rift \q -> f (q :.: p))
  corepMap (Prof f) = Prof \(j :.: p) -> j :.: f p

instance (p ~ j, Profunctor p) => Promonad (Rift (OP j) p) where
  id = Rift id
  Rift l . Rift r = Rift (l . r)

instance (HasColimits j k, Corepresentable d) => Corepresentable (Rift (OP j) (d :: k +-> i)) where
  type Rift (OP j) d %% a = Colimit j d %% a
  coindex = coindex @(Colimit j d) . colimitUniv @j @k @d (\(j :.: Rift k') -> k' j)
  cotabulate f = Rift (\j -> colimit (j :.: cotabulate f)) \\ f
  corepMap = corepMap @(Colimit j d)

type PWLan j p a = (p <| j) %% a
-- PWLan j p a ~> b = forall x. j x ~> a -> p x ~> b
-- PWLan j p a ~> b = forall x. ((j x ~> a) .* p x) ~> b
-- PWLan j p a = exists x. ((j x ~> a) .* p x)
class (Corepresentable j, Corepresentable p, Corepresentable (p <| j)) => PointwiseLeftKanExtension j p
instance (Corepresentable j, Corepresentable p, Corepresentable (p <| j)) => PointwiseLeftKanExtension j p

type PWRift j p a = (p <| j) % a
-- a ~> PWRift j p b = forall x. x ~> j a -> x ~> p b
-- a ~> PWRift j p b = j a ~> p b
class (Representable p, Representable j, Representable (p <| j)) => PointwiseRightKanLift j p
instance (Representable p, Representable j, Representable (p <| j)) => PointwiseRightKanLift j p

riftCompose :: (Profunctor i, Profunctor j, Profunctor p) => (p <| j) <| i ~> p <| (j :.: i)
riftCompose = Prof \k -> k // Rift \(j :.: i) -> runRift j (runRift i k)

riftComposeInv :: (Profunctor i, Profunctor j, Profunctor p) => p <| (j :.: i) ~> (p <| j) <| i
riftComposeInv = Prof \k -> k // Rift \i -> i // Rift \j -> runRift (j :.: i) k
