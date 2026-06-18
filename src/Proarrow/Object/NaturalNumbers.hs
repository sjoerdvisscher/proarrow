module Proarrow.Object.NaturalNumbers where

import Data.Kind (Type)
import Data.Nat qualified as N

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Object.BinaryProduct ()

class (SymMonoidal k, Ob (NNO :: k)) => HasParamNNO k where
  type NNO :: k
  zero :: Unit ~> (NNO :: k)
  succ :: NNO ~> (NNO :: k)
  nnoUniv :: forall (a :: k) x. a ~> x -> x ~> x -> a ** NNO ~> x

add :: forall {k}. (HasParamNNO k) => NNO ** NNO ~> (NNO :: k)
add = nnoUniv id succ

instance HasParamNNO () where
  type NNO = '()
  zero = U.Unit
  succ = U.Unit
  nnoUniv z _ = U.Unit \\ z

instance (HasParamNNO j, HasParamNNO k) => HasParamNNO (j, k) where
  type NNO = '(NNO, NNO)
  zero = zero :**: zero
  succ = succ :**: succ
  nnoUniv (z1 :**: z2) (s1 :**: s2) = nnoUniv z1 s1 :**: nnoUniv z2 s2

instance HasParamNNO Type where
  type NNO = N.Nat
  zero () = N.Z
  succ = N.S
  nnoUniv z s (a, n) = N.cata (z a) s n