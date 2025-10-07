{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Object (obj, Obj)
import Proarrow.Functor (FunctorForRep (..))

infixl 8 %%

type Corepresentable :: forall {j} {k}. (j +-> k) -> Constraint
class (Profunctor p) => Corepresentable (p :: j +-> k) where
  type p %% (a :: k) :: j
  coindex :: p a b -> p %% a ~> b
  cotabulate :: (Ob a) => (p %% a ~> b) -> p a b
  corepMap :: (a ~> b) -> p %% a ~> p %% b

instance Corepresentable (->) where
  type (->) %% a = a
  coindex f = f
  cotabulate f = f
  corepMap f = f

corepObj :: forall p a. (Corepresentable p, Ob a) => Obj (p %% a)
corepObj = corepMap @p (obj @a)

withCorepOb :: forall p a r. (Corepresentable p, Ob a) => ((Ob (p %% a)) => r) -> r
withCorepOb r = r \\ corepMap @p (obj @a)

dimapCorep :: forall p a b c d. (Corepresentable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapCorep l r = cotabulate @p . dimap (corepMap @p l) r . coindex \\ l

trivialCorep :: forall p a. (Corepresentable p, Ob a) => p a (p %% a)
trivialCorep = cotabulate (corepObj @p @a)

type Corep :: (j +-> k) -> (k +-> j)
data Corep f a b where
  Corep :: (Ob a) => {unCorep :: f @ a ~> b} -> Corep f a b
instance (FunctorForRep f) => Profunctor (Corep f) where
  dimap = dimapCorep
  r \\ Corep f = r \\ f
instance (FunctorForRep f) => Corepresentable (Corep f) where
  type Corep f %% a = f @ a
  coindex (Corep f) = f
  cotabulate = Corep
  corepMap = fmap @f