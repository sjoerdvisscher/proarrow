{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Representable where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Object (Obj, obj)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))

infixl 8 %

type Representable :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => Representable (p :: j +-> k) where
  type p % (a :: j) :: k
  index :: p a b -> a ~> p % b
  tabulate :: (Ob b) => (a ~> p % b) -> p a b
  repMap :: (a ~> b) -> p % a ~> p % b

repObj :: forall p a. (Representable p, Ob a) => Obj (p % a)
repObj = repMap @p (obj @a)

withRepObj :: forall p a r. (Representable p, Ob a) => ((Ob (p % a)) => r) -> r
withRepObj r = r \\ repObj @p @a

dimapRep :: forall p a b c d. (Representable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapRep l r = tabulate @p . dimap l (repMap @p r) . index \\ r

type RepStar :: (j +-> k) -> (j +-> k)
data RepStar p a b where
  RepStar :: (Ob b) => {unRepStar :: a ~> p % b} -> RepStar p a b
instance (Representable p) => Profunctor (RepStar p) where
  dimap f g (RepStar h) = RepStar (repMap @p g . h . f) \\ g
  r \\ RepStar f = r \\ f
instance (Representable p) => Representable (RepStar p) where
  type RepStar p % a = p % a
  index (RepStar f) = f
  tabulate = RepStar
  repMap = repMap @p

type RepCostar :: (k +-> j) -> (j +-> k)
data RepCostar p a b where
  RepCostar :: (Ob a) => {unRepCostar :: p % a ~> b} -> RepCostar p a b
instance (Representable p) => Profunctor (RepCostar p) where
  dimap f g (RepCostar h) = RepCostar (g . h . repMap @p f) \\ f
  r \\ RepCostar f = r \\ f
instance (Representable p) => Corepresentable (RepCostar p) where
  type RepCostar p %% a = p % a
  coindex (RepCostar f) = f
  cotabulate = RepCostar
  corepMap = repMap @p