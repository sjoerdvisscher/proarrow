{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Functor where

import Data.Functor.Const (Const (..))
import Data.Kind (Constraint, Type)
import Prelude (const, fmap)

import Proarrow.Core (Category(..), CategoryOf, type (~>), (\\))
import Proarrow.Object (Obj, obj)

infixr 0 .~>
type f .~> g = forall a. Ob a => f a ~> g a

type Functor :: forall {k1} {k2}. (k1 -> k2) -> Constraint
class (CategoryOf k1, CategoryOf k2) => Functor (f :: k1 -> k2) where
  map :: a ~> b -> f a ~> f b

withFCod' :: forall f a r. (Functor f, Ob a) => (Ob (f a) => Obj (f a) -> r) -> r
withFCod' r = let o = map @f (obj @a) in r o \\ o

withFCod :: forall f a r. (Functor f, Ob a) => (Ob (f a) => r) -> r
withFCod r = withFCod' @f @a (const r)


instance Functor ((,) a) where
  map = fmap

instance Functor ((->) a) where
  map = fmap

instance CategoryOf k => Functor (Const x :: k -> Type) where
  map _ (Const x) = Const x
