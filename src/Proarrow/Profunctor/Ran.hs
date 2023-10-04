{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Proarrow.Profunctor.Ran where

import Proarrow.Core (PRO, Category(..), Profunctor(..), (//), rmap)
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Category.Opposite (OPPOSITE(..), Op(..))
import Proarrow.Adjunction (Adjunction (..), unitFromStarUnit, counitFromStarCounit)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Profunctor.Star (Star(..))

type j |> p = Ran (OP j) p

type Ran :: OPPOSITE (PRO i j) -> PRO i k -> PRO j k
data Ran j p a b where
  Ran :: (Ob a, Ob b) => { getRan :: forall x. Ob x => j x a -> p x b } -> Ran (OP j) p a b

runRan :: Profunctor j => j x a -> Ran (OP j) p a b -> p x b
runRan j (Ran k) = k j \\ j

instance (Profunctor p, Profunctor j) => Profunctor (Ran (OP j) p) where
  dimap l r (Ran k) = l // r // Ran (rmap r . k . rmap l)
  r \\ Ran{} = r

instance Profunctor j => Functor (Ran (OP j)) where
  map (Prof n) = Prof \(Ran k) -> Ran (n . k)

instance Functor Ran where
  map (Op (Prof n)) = Nat (Prof \(Ran k) -> Ran (k . n))

instance Profunctor j => Adjunction (Star ((:.:) j)) (Star (Ran (OP j))) where
  unit = unitFromStarUnit (Prof \p -> p // Ran (:.: p))
  counit = counitFromStarCounit (Prof \(j :.: r) -> runRan j r)
