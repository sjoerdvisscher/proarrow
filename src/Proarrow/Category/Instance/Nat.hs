{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Instance.Nat where

import Proarrow.Core (CAT, CategoryOf(..), Promonad(..), Profunctor(..), Is, UN, dimapDefault)
import Proarrow.Functor (Functor(..), type (.~>))
import Data.Kind (Type)

type Nat :: CAT (j -> k)
data Nat f g where
  Nat :: (Functor f, Functor g)
      => { getNat :: f .~> g }
      -> Nat f g

instance CategoryOf (k1 -> Type) where
  type instance (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (j -> Type)) where
  id = n where
    n :: forall f. Functor f => Nat f f
    n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> Type)) where
  dimap = dimapDefault
  r \\ Nat{} = r


instance CategoryOf (k1 -> k2 -> k3 -> Type) where
  type instance (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (k1 -> k2 -> k3 -> Type)) where
  id = n where
    n :: forall f. Functor f => Nat f f
    n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> k2 -> k3 -> Type)) where
  dimap f g h = g . h . f
  r \\ Nat{} = r


instance CategoryOf (k1 -> k2 -> k3 -> k4 -> Type) where
  type instance (~>) = Nat
  type Ob f = Functor f

instance Promonad (Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)) where
  id = n where
    n :: forall f. Functor f => Nat f f
    n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)) where
  dimap f g h = g . h . f
  r \\ Nat{} = r



newtype NatK j k = NT (j -> k)
type instance UN NT (NT f) = f

data Nat' f g where
  Nat' :: (Functor f, Functor g)
       => { getNat' :: f .~> g }
       -> Nat' (NT f) (NT g)

instance CategoryOf (NatK j k) where
  type instance (~>) = Nat'
  type Ob f = (Is NT f, Functor (UN NT f))

instance Promonad (Nat' :: CAT (NatK j k)) where
  id = n where
    n :: forall f. Functor f => Nat' (NT f) (NT f)
    n = Nat' (map @f id)
  Nat' f . Nat' g = Nat' (f . g)

instance Profunctor (Nat' :: CAT (NatK j k)) where
  dimap = dimapDefault
  r \\ Nat'{} = r
