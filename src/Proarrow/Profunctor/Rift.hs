module Proarrow.Profunctor.Rift where

import Proarrow.Core (PRO, Category(..), Profunctor(..), (//), lmap)
import Proarrow.Functor (Functor(..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Nat (Nat(..))
import Proarrow.Category.Opposite (OP(..), Op(..))
import Proarrow.Adjunction (Adjunction (..), unitFromStarUnit, counitFromStarCounit)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Profunctor.Star (Star(..))

type p <| j = Rift ('OP j) p

type Rift :: OP (PRO k2 k3) -> PRO k1 k3 -> PRO k1 k2
data Rift j p a b where
  Rift :: (Ob a, Ob b) => { getRift :: forall x. Ob x => j b x -> p a x } -> Rift ('OP j) p a b

runRift :: Profunctor j => j b x -> Rift ('OP j) p a b -> p a x
runRift j (Rift k) = k j \\ j

instance (Profunctor p, Profunctor j) => Profunctor (Rift ('OP j) p) where
  dimap l r (Rift k) = r // l // Rift (lmap l . k . lmap r)
  r \\ Rift{} = r

instance Profunctor j => Functor (Rift ('OP j)) where
  map (Prof n) = Prof \(Rift k) -> Rift (n . k)

instance Functor Rift where
  map (Op (Prof n)) = Nat (Prof \(Rift k) -> Rift (k . n))

-- instance Profunctor j => Adjunction (Star ((:.:) j)) (Star (Rift ('OP j))) where
--   unit = unitFromStarUnit (Prof \a -> Rift (a :.:) \\ a)
--   counit = counitFromStarCounit (Prof \(j :.: r) -> runRift j r)