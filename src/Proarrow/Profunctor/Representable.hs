{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Representable where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->), (:~>))
import Proarrow.Object (Obj, obj)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), dimapCorep)

infixl 8 %

type Representable :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => Representable (p :: j +-> k) where
  type p % (a :: j) :: k
  index :: p a b -> a ~> p % b
  tabulate :: (Ob b) => (a ~> p % b) -> p a b
  repMap :: (a ~> b) -> p % a ~> p % b

instance Representable (->) where
  type (->) % a = a
  index f = f
  tabulate f = f
  repMap f = f

repObj :: forall p a. (Representable p, Ob a) => Obj (p % a)
repObj = repMap @p (obj @a)

withRepOb :: forall p a r. (Representable p, Ob a) => ((Ob (p % a)) => r) -> r
withRepOb r = r \\ repObj @p @a

dimapRep :: forall p a b c d. (Representable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapRep l r = tabulate @p . dimap l (repMap @p r) . index \\ r

type RepStar :: (j +-> k) -> (j +-> k)
data RepStar p a b where
  RepStar :: (Ob b) => {unRepStar :: a ~> p % b} -> RepStar p a b
instance (Representable p) => Profunctor (RepStar p) where
  dimap = dimapRep
  r \\ RepStar f = r \\ f
instance (Representable p) => Representable (RepStar p) where
  type RepStar p % a = p % a
  index (RepStar f) = f
  tabulate = RepStar
  repMap = repMap @p

type CorepStar :: (k +-> j) -> (j +-> k)
data CorepStar p a b where
  CorepStar :: (Ob b) => {unCorepStar :: a ~> p %% b} -> CorepStar p a b
instance (Corepresentable p) => Profunctor (CorepStar p) where
  dimap = dimapRep
  r \\ CorepStar f = r \\ f
instance (Corepresentable p) => Representable (CorepStar p) where
  type CorepStar p % a = p %% a
  index (CorepStar f) = f
  tabulate = CorepStar
  repMap = corepMap @p

type RepCostar :: (k +-> j) -> (j +-> k)
data RepCostar p a b where
  RepCostar :: (Ob a) => {unRepCostar :: p % a ~> b} -> RepCostar p a b
instance (Representable p) => Profunctor (RepCostar p) where
  dimap = dimapCorep
  r \\ RepCostar f = r \\ f
instance (Representable p) => Corepresentable (RepCostar p) where
  type RepCostar p %% a = p % a
  coindex (RepCostar f) = f
  cotabulate = RepCostar
  corepMap = repMap @p

flipRep :: forall p q. (Representable p, Corepresentable q) => RepCostar p :~> q -> CorepStar q :~> p
flipRep n (CorepStar @b q) = tabulate @p (coindex @q @b (n (RepCostar (repMap @p (obj @b)))) . q)