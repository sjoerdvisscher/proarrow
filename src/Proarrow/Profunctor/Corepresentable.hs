{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Object (obj, Obj)

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

type Corep :: (j +-> k) -> (j +-> k)
data Corep p a b where
  Corep :: Ob a => { getCorep :: p %% a ~> b } -> Corep p a b
instance (Corepresentable p) => Profunctor (Corep p) where
  dimap f g (Corep h) = Corep (g . h . corepMap @p f) \\ f
  r \\ Corep f = r \\ f
instance (Corepresentable p) => Corepresentable (Corep p) where
  type Corep p %% a = p %% a
  coindex (Corep f) = f
  cotabulate = Corep
  corepMap = corepMap @p