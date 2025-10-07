{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Functor where

import Data.Functor.Compose (Compose (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty qualified as P
import Prelude qualified as P

import Proarrow.Core (CategoryOf (..), Promonad (..), Profunctor, rmap, type (+->))
import Proarrow.Object (Ob')

infixr 0 .~>
type f .~> g = forall a. (Ob a) => f a ~> g a

type Functor :: forall {k1} {k2}. (k1 -> k2) -> Constraint
class (CategoryOf k1, CategoryOf k2, forall a. (Ob a) => Ob' (f a)) => Functor (f :: k1 -> k2) where
  map :: a ~> b -> f a ~> f b

-- Can't make an instance Functor (f :: Type -> Type) because that would overlap with instances of kind k -> Type
newtype Prelude (f :: Type -> Type) a = Prelude {unPrelude :: f a}
  deriving (P.Functor, P.Foldable, P.Traversable, P.Eq, P.Show)
instance (P.Functor f) => Functor (Prelude f) where
  map f = Prelude . P.fmap f . unPrelude

deriving via Prelude ((,) a) instance Functor ((,) a)
deriving via Prelude (P.Either a) instance Functor (P.Either a)
deriving via Prelude P.IO instance Functor P.IO
deriving via Prelude P.Maybe instance Functor P.Maybe
deriving via Prelude P.NonEmpty instance Functor P.NonEmpty
deriving via Prelude ((->) a) instance Functor ((->) a)
deriving via Prelude [] instance Functor []
deriving via Prelude Identity instance Functor Identity

instance (CategoryOf k) => Functor (Const x :: k -> Type) where
  map _ (Const x) = Const x

instance (Functor f, Functor g) => Functor (Compose f g) where
  map f = Compose . map (map f) . getCompose

newtype FromProfunctor p a b = FromProfunctor {unFromProfunctor :: p a b}
instance (Profunctor p) => Functor (FromProfunctor p a) where
  map f = FromProfunctor . rmap f . unFromProfunctor
instance (Profunctor p) => P.Functor (FromProfunctor p a) where
  fmap = map

-- | Presheaves are functors but it makes more sense in proarrow to represent them as profunctors from the unit category.
type Presheaf k = () +-> k
-- | Copresheaves are functors but it makes more sense in proarrow to represent them as profunctors into the unit category.
type Copresheaf k = k +-> ()

-- | A perfectly valid functor definition, but hard to use.
-- So we only use it to easily make representable profunctors with @Rep@.
type FunctorForRep :: forall {j} {k}. (j +-> k) -> Constraint
class (CategoryOf j, CategoryOf k) => FunctorForRep (f :: j +-> k) where
  type f @ (a :: j) :: k
  fmap :: (a ~> b) -> f @ a ~> f @ b
