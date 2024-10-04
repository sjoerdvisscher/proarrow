module Proarrow.Profunctor.Rift where

import Prelude (type (~))

import Proarrow.Adjunction (Adjunction (..), counitFromRepCounit, unitFromRepUnit)
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, (//), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star (..))

-- Note: Ran and Rift are swapped compared to the profunctors package.

type p <| j = Rift (OP j) p

type Rift :: OPPOSITE (k +-> i) -> j +-> i -> j +-> k
data Rift j p a b where
  Rift :: (Ob a, Ob b) => {unRift :: forall x. (Ob x) => j x a -> p x b} -> Rift (OP j) p a b

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

instance (Profunctor j) => Adjunction (Star ((:.:) j)) (Star (Rift (OP j))) where
  unit = unitFromRepUnit (Prof \p -> p // Rift (:.: p))
  counit = counitFromRepCounit (Prof \(j :.: r) -> runRift j r)

instance (p ~ j, Profunctor p) => Promonad (Rift (OP p) p) where
  id = Rift id
  Rift l . Rift r = Rift (l . r)

riftCompose :: (Profunctor i, Profunctor j, Profunctor p) => (p <| j) <| i ~> p <| (j :.: i)
riftCompose = Prof \k -> k // Rift \(j :.: i) -> runRift j (runRift i k)

riftComposeInv :: (Profunctor i, Profunctor j, Profunctor p) => p <| (j :.: i) ~> (p <| j) <| i
riftComposeInv = Prof \k -> k // Rift \i -> Rift \j -> runRift (j :.: i) k
