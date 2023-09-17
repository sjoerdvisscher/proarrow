module Proarrow.Category.Instance.Nat where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)
import Proarrow.Functor (Functor(..), type (.~>))
import Data.Kind (Type)

type Nat :: CAT (k1 -> k2)
data Nat f g where
  Nat :: (Functor f, Functor g)
      => { getNat :: f .~> g }
      -> Nat f g


type instance (~>) = Nat :: CAT (k1 -> Type)

instance Category (Nat :: CAT (k1 -> Type)) where
  type Ob f = Functor f
  id = n where
    n :: forall f. Functor f => Nat f f
    n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> Type)) where
  dimap = dimapDefault
  r \\ Nat{} = r


type instance (~>) = Nat :: CAT (k1 -> k2 -> k3 -> Type)

instance Category (Nat :: CAT (k1 -> k2 -> k3 -> Type)) where
  type Ob f = Functor f
  id = n where
    n :: forall f. Functor f => Nat f f
    n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> k2 -> k3 -> Type)) where
  dimap f g h = g . h . f
  r \\ Nat{} = r


type instance (~>) = Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)

instance Category (Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)) where
  type Ob f = Functor f
  id = n where
    n :: forall f. Functor f => Nat f f
    n = Nat (map @f id)
  Nat f . Nat g = Nat (f . g)

instance Profunctor (Nat :: CAT (k1 -> k2 -> k3 -> k4 -> Type)) where
  dimap f g h = g . h . f
  r \\ Nat{} = r