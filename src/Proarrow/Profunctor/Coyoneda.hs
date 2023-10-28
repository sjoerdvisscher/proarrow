module Proarrow.Profunctor.Coyoneda where

import Data.Kind (Type)

import Proarrow.Core (PRO, CategoryOf(..), Promonad(..), Profunctor(..))

type Coyoneda :: (j -> k -> Type) -> PRO j k
data Coyoneda p a b where
  Coyoneda :: (a ~> c) -> (d ~> b) -> p c d -> Coyoneda p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Coyoneda (p :: j -> k -> Type)) where
  dimap l r (Coyoneda f g p) = Coyoneda (f . l) (r . g) p
  r \\ Coyoneda f g _ = r \\ f \\ g

coyoneda :: (CategoryOf j, CategoryOf k, Ob a, Ob b) => p a b -> Coyoneda (p :: j -> k -> Type) a b
coyoneda = Coyoneda id id
