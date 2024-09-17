{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Profunctor.Coyoneda where

import Data.Kind (Type)

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), (:~>))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Free (HasFree (..))
import Proarrow.Profunctor.Star (Star (..))

type Coyoneda :: (j -> k -> Type) -> PRO j k
data Coyoneda p a b where
  Coyoneda :: (a ~> c) -> (d ~> b) -> p c d -> Coyoneda p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Coyoneda (p :: j -> k -> Type)) where
  dimap l r (Coyoneda f g p) = Coyoneda (f . l) (r . g) p
  r \\ Coyoneda f g _ = r \\ f \\ g

instance (Functor Coyoneda) where
  map (Prof n) = Prof \(Coyoneda g h p) -> Coyoneda g h (n p)

instance HasFree Profunctor where
  type Free Profunctor = Star Coyoneda
  lift' (Prof n) = Star (Prof \p -> coyoneda (n p) \\ p)
  retract' (Star (Prof f)) = Prof (unCoyoneda . f)

coyoneda :: (CategoryOf j, CategoryOf k, Ob a, Ob b) => p a b -> Coyoneda (p :: j -> k -> Type) a b
coyoneda = Coyoneda id id

unCoyoneda :: (Profunctor p) => Coyoneda p :~> p
unCoyoneda (Coyoneda f g p) = dimap f g p