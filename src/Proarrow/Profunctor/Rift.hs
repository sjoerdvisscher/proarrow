module Proarrow.Profunctor.Rift where

import Proarrow.Adjunction (Adjunction (..), counitFromRepCounit, unitFromRepUnit)
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), lmap, (//))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Star (Star (..))

type p <| j = Rift (OP j) p

type Rift :: OPPOSITE (PRO k i) -> PRO j i -> PRO j k
data Rift j p a b where
  Rift :: (Ob a, Ob b) => {unRift :: forall x. (Ob x) => j b x -> p a x} -> Rift (OP j) p a b

runRift :: (Profunctor j) => j b x -> Rift (OP j) p a b -> p a x
runRift j (Rift k) = k j \\ j

instance (Profunctor p, Profunctor j) => Profunctor (Rift (OP j) p) where
  dimap l r (Rift k) = r // l // Rift (lmap l . k . lmap r)
  r \\ Rift{} = r

instance (Profunctor j) => Functor (Rift (OP j)) where
  map (Prof n) = Prof \(Rift k) -> Rift (n . k)

instance Functor Rift where
  map (Op (Prof n)) = Nat (Prof \(Rift k) -> Rift (k . n))

newtype Precompose j p a b = Precompose {unPrecompose :: (p :.: j) a b}
instance (Profunctor j, Profunctor p) => Profunctor (Precompose j p) where
  dimap l r (Precompose pj) = Precompose (dimap l r pj)
  r \\ Precompose pj = r \\ pj
instance (Profunctor j) => Functor (Precompose j) where
  map f = f // Prof \(Precompose pj) -> Precompose (unProf (unNat (map f)) pj)

instance (Profunctor j) => Adjunction (Star (Precompose j)) (Star (Rift (OP j))) where
  unit = unitFromRepUnit (Prof \p -> p // Rift \j -> Precompose (p :.: j))
  counit = counitFromRepCounit (Prof \(Precompose (r :.: j)) -> runRift j r)

riftCompose :: (Profunctor i, Profunctor j, Profunctor p) => (p <| j) <| i ~> p <| (i :.: j)
riftCompose = Prof \k -> k // Rift \(i :.: j) -> runRift j (runRift i k)

riftComposeInv :: (Profunctor i, Profunctor j, Profunctor p) => p <| (i :.: j) ~> (p <| j) <| i
riftComposeInv = Prof \k -> k // Rift \i -> Rift \j -> runRift (i :.: j) k
