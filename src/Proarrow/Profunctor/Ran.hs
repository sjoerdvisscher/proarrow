{-# LANGUAGE DerivingStrategies #-}

module Proarrow.Profunctor.Ran where

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

type j |> p = Ran (OP j) p

type Ran :: OPPOSITE (i +-> j) -> i +-> k -> j +-> k
data Ran j p a b where
  Ran :: (Ob a, Ob b) => {unRan :: forall x. (Ob x) => j b x -> p a x} -> Ran (OP j) p a b

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

instance (p ~ j, Profunctor p) => Promonad (Ran (OP p) p) where
  id = Ran id
  Ran l . Ran r = Ran (r . l)

newtype Precompose j p a b = Precompose {unPrecompose :: (p :.: j) a b}
instance (Profunctor j, Profunctor p) => Profunctor (Precompose j p) where
  dimap l r (Precompose pj) = Precompose (dimap l r pj)
  r \\ Precompose pj = r \\ pj
instance (Profunctor j) => Functor (Precompose j) where
  map f = f // Prof \(Precompose pj) -> Precompose (unProf (unNat (map f)) pj)

instance (Profunctor j) => Adjunction (Star (Precompose j)) (Star (Ran (OP j))) where
  unit = unitFromRepUnit (Prof \p -> p // Ran \j -> Precompose (p :.: j))
  counit = counitFromRepCounit (Prof \(Precompose (r :.: j)) -> runRan j r)

riftCompose :: (Profunctor i, Profunctor j, Profunctor p) => i |> (j |> p) ~> (i :.: j) |> p
riftCompose = Prof \k -> k // Ran \(i :.: j) -> runRan j (runRan i k)

riftComposeInv :: (Profunctor i, Profunctor j, Profunctor p) => (i :.: j) |> p ~> i |> (j |> p)
riftComposeInv = Prof \k -> k // Ran \i -> Ran \j -> runRan (i :.: j) k
