{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Representable where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..))
import Proarrow.Object (obj)

infixl 8 %

type Representable :: forall {j} {k}. PRO j k -> Constraint
class (Profunctor p) => Representable (p :: PRO j k) where
  type p % (a :: k) :: j
  index :: p a b -> a ~> p % b
  tabulate :: (Ob b) => (a ~> p % b) -> p a b
  repMap :: (a ~> b) -> p % a ~> p % b

withRepCod :: forall p a r. (Representable p, Ob a) => ((Ob (p % a)) => r) -> r
withRepCod r = r \\ repMap @p (obj @a)

dimapRep :: forall p a b c d. (Representable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapRep l r = tabulate @p . dimap l (repMap @p r) . index \\ r
