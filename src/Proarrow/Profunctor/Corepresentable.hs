{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..))
import Proarrow.Object (obj)

infixl 8 %%

type Corepresentable :: forall {j} {k}. PRO j k -> Constraint
class (Profunctor p) => Corepresentable (p :: PRO j k) where
  type p %% (a :: j) :: k
  coindex :: p a b -> p %% a ~> b
  cotabulate :: (Ob a) => (p %% a ~> b) -> p a b
  corepMap :: (a ~> b) -> p %% a ~> p %% b

withCorepCod :: forall p a r. (Corepresentable p, Ob a) => ((Ob (p %% a)) => r) -> r
withCorepCod r = r \\ corepMap @p (obj @a)

dimapCorep :: forall p a b c d. (Corepresentable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapCorep l r = cotabulate @p . dimap (corepMap @p l) r . coindex \\ l
