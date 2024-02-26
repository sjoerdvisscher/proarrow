module Proarrow.Functor where

import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity)
import Data.Functor.Compose (Compose(..))
import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Core (CategoryOf(..), Promonad(..))
import Proarrow.Object (Ob')

infixr 0 .~>
type f .~> g = forall a. Ob a => f a ~> g a

type Functor :: forall {k1} {k2}. (k1 -> k2) -> Constraint
class (CategoryOf k1, CategoryOf k2, forall a. Ob a => Ob' (f a)) => Functor (f :: k1 -> k2) where
  map :: a ~> b -> f a ~> f b


newtype Prelude f a = Prelude { getPrelude :: f a }
instance P.Functor f => Functor (Prelude f) where
  map f = Prelude . P.fmap f . getPrelude

deriving via Prelude ((,) a) instance Functor ((,) a)
deriving via Prelude (P.Either a) instance Functor (P.Either a)
deriving via Prelude ((->) a) instance Functor ((->) a)
deriving via Prelude [] instance Functor []
deriving via Prelude Identity instance Functor Identity

instance CategoryOf k => Functor (Const x :: k -> Type) where
  map _ (Const x) = Const x

instance (Functor f, Functor g) => Functor (Compose f g) where
  map f = Compose . map (map f) . getCompose