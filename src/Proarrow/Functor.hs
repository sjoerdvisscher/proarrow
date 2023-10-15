module Proarrow.Functor where

import Data.Functor.Const (Const (..))
import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Core (Category(..), CategoryOf, type (~>))

infixr 0 .~>
type f .~> g = forall a. Ob a => f a ~> g a

class Ob (f a) => ObFun f a
instance Ob (f a) => ObFun f a

type Functor :: forall {k1} {k2}. (k1 -> k2) -> Constraint
class (CategoryOf k1, CategoryOf k2, forall a. Ob a => ObFun f a) => Functor (f :: k1 -> k2) where
  map :: a ~> b -> f a ~> f b


newtype Prelude f a = Prelude { getPrelude :: f a }
instance P.Functor f => Functor (Prelude f) where
  map f = Prelude . P.fmap f . getPrelude

deriving via Prelude ((,) a) instance Functor ((,) a)
deriving via Prelude ((->) a) instance Functor ((->) a)
deriving via Prelude [] instance Functor []

instance CategoryOf k => Functor (Const x :: k -> Type) where
  map _ (Const x) = Const x
