{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..))
import Proarrow.Object (obj)

infixl 8 %%

type Corepresentable :: forall {j} {k}. PRO j k -> Constraint
class Profunctor p => Corepresentable (p :: PRO j k) where
  type p %% (a :: j) :: k
  coindex :: p a b -> p %% a ~> b
  cotabulate :: Ob a => (p %% a ~> b) -> p a b
  corepMap :: (a ~> b) -> p %% a ~> p %% b

withCorepCod :: forall p a r. (Corepresentable p, Ob a) => (Ob (p %% a) => r) -> r
withCorepCod r = r \\ corepMap @p (obj @a)
