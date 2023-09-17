{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Core (PRO, Category(..), Profunctor(..), type (~>))
import Proarrow.Object (obj)

type Corepresentable :: forall {k1} {k2}. PRO k1 k2 -> Constraint
class Profunctor p => Corepresentable (p :: PRO k1 k2) where
  type p %% (a :: k1) :: k2
  coindex :: p a b -> p %% a ~> b
  cotabulate :: Ob a => (p %% a ~> b) -> p a b
  corepMap :: (a ~> b) -> p %% a ~> p %% b

withCorepCod :: forall p a r. (Corepresentable p, Ob a) => (Ob (p %% a) => r) -> r
withCorepCod r = r \\ corepMap @p (obj @a)
