{-# LANGUAGE DerivingStrategies #-}

module Proarrow.Profunctor.Ran where

import Proarrow.Adjunction (Adjunction (..), counitFromRepCounit, unitFromRepUnit)
import Proarrow.Category.Instance.Nat (Nat (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), lmap, rmap, (//))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star (..))

type j |> p = Ran (OP j) p

type Ran :: OPPOSITE (PRO i j) -> PRO i k -> PRO j k
data Ran j p a b where
  Ran :: (Ob a, Ob b) => {unRan :: forall x. (Ob x) => j x a -> p x b} -> Ran (OP j) p a b

runRan :: (Profunctor j) => j x a -> Ran (OP j) p a b -> p x b
runRan j (Ran k) = k j \\ j

flipRan :: (Functor j, Profunctor p) => Star j |> p ~> Costar j :.: p
flipRan = Prof \(Ran k) -> Costar id :.: k (Star id)

flipRanInv :: (Functor j, Profunctor p) => Costar j :.: p ~> Star j |> p
flipRanInv = Prof \(Costar f :.: p) -> p // Ran \(Star g) -> lmap (f . g) p

instance (Profunctor p, Profunctor j) => Profunctor (Ran (OP j) p) where
  dimap l r (Ran k) = l // r // Ran (rmap r . k . rmap l)
  r \\ Ran{} = r

instance (Profunctor j) => Functor (Ran (OP j)) where
  map (Prof n) = Prof \(Ran k) -> Ran (n . k)

instance Functor Ran where
  map (Op (Prof n)) = Nat (Prof \(Ran k) -> Ran (k . n))

instance (Profunctor j) => Adjunction (Star ((:.:) j)) (Star (Ran (OP j))) where
  unit = unitFromRepUnit (Prof \p -> p // Ran (:.: p))
  counit = counitFromRepCounit (Prof \(j :.: r) -> runRan j r)

ranCompose :: (Profunctor i, Profunctor j, Profunctor p) => i |> (j |> p) ~> (j :.: i) |> p
ranCompose = Prof \k -> k // Ran \(j :.: i) -> runRan j (runRan i k)

ranComposeInv :: (Profunctor i, Profunctor j, Profunctor p) => (j :.: i) |> p ~> i |> (j |> p)
ranComposeInv = Prof \k -> k // Ran \i -> Ran \j -> runRan (j :.: i) k
