{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Profunctor.Representable where

import Data.Kind (Constraint)

import Proarrow.Core (PRO, CategoryOf(..), Profunctor(..))
import Proarrow.Object (obj)

infixl 8 %

type Representable :: forall {j} {k}. PRO j k -> Constraint
class Profunctor p => Representable (p :: PRO j k) where
  type p % (a :: k) :: j
  index :: p a b -> a ~> p % b
  tabulate :: Ob b => (a ~> p % b) -> p a b
  repMap :: (a ~> b) -> p % a ~> p % b

withRepCod :: forall p a r. (Representable p, Ob a) => (Ob (p % a) => r) -> r
withRepCod r = r \\ repMap @p (obj @a)
