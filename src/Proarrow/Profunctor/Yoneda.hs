{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Profunctor.Yoneda where

import Data.Kind (Type)

import Proarrow.Core (PRO, CategoryOf, Category(..), Profunctor(..), type (~>), (//))

type Yoneda :: (j -> k -> Type) -> PRO j k
data Yoneda p a b where
  Yoneda :: (Ob a, Ob b) => { getYoneda :: forall c d. (c ~> a) -> (b ~> d) -> p c d } -> Yoneda p a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Yoneda (p :: j -> k -> Type)) where
  dimap l r (Yoneda k) = l // r // Yoneda \ca bd -> k (l . ca) (bd . r)
  r \\ Yoneda{} = r

yoneda :: (CategoryOf j, CategoryOf k, Ob a, Ob b) => Yoneda (p :: j -> k -> Type) a b -> p a b
yoneda (Yoneda k) = k id id
