{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Category.Enriched where

import Data.Kind (Constraint, Type)
import Prelude (uncurry)

import Proarrow.Category.Opposite (OPPOSITE(..), Op (..))
import Proarrow.Core (Promonad(..), CategoryOf(..), PRO, Profunctor (..))
import Proarrow.Object.BinaryProduct (HasProducts, type (&&))
import Proarrow.Object.Terminal (TerminalObject)
import Proarrow.Profunctor.Representable (Representable(..), dimapRep)
import Proarrow.Category.Instance.Product ((:**:)(..))


type EPRO v j k = PRO v (OPPOSITE j, k) -- a functor J^op x K -> V as a representable profunctor
type ECAT v k = EPRO v k k

class (HasProducts v, Representable p) => ECategory (p :: ECAT v k) where
  type EOb p (a :: k) :: Constraint
  eid :: EOb p a => TerminalObject ~> p % '(OP a, a)
  ecomp :: p % '(OP b, c) && p % '(OP a, b) ~> p % '(OP a, c)



type TypeCat :: ECAT Type k
data TypeCat a bc where
  TypeCat :: (Ob b, Ob c) => (a -> b ~> c) -> TypeCat a '(OP b, c)

instance CategoryOf k => Profunctor (TypeCat :: ECAT Type k) where
  dimap = dimapRep
  r \\ TypeCat f = r \\ f

instance CategoryOf k => Representable (TypeCat :: ECAT Type k) where
  type TypeCat % '(OP a, b) = a ~> b
  index (TypeCat f) = f
  tabulate = TypeCat
  repMap (Op f :**: g) = dimap f g

instance CategoryOf k => ECategory (TypeCat :: ECAT Type k) where
  type EOb TypeCat a = Ob a
  eid () = id
  ecomp = uncurry (.)
