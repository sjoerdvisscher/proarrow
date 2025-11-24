module Proarrow.Universal where

import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction)
import Proarrow.Core (CategoryOf (..), Profunctor (..), lmap, rmap, type (+->))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep)
import Proarrow.Profunctor.Representable (Representable (..), trivialRep)

-- | The initial universal property of a functor @r@ (as a representable profunctor) and an object @a@.
type InitUniversal :: forall {j} {k}. (j +-> k) -> k -> Constraint
class (Representable r, Ob a) => InitUniversal (r :: j +-> k) (a :: k) where
  type L r a :: j
  initUnivArr :: r a (L r a)
  initUnivProp :: r a b -> L r a ~> b

-- | The terminal universal property of a functor @l@ (as a corepresentable profunctor) and an object @b@.
type TermUniversal :: forall {j} {k}. (j +-> k) -> j -> Constraint
class (Corepresentable l, Ob b) => TermUniversal (l :: j +-> k) (b :: j) where
  type R l b :: k
  termUnivArr :: l (R l b) b
  termUnivProp :: l a b -> a ~> R l b

newtype AsRightAdjoint r a b = AsRightAdjoint {unAsRightAdjoint :: r a b}
  deriving newtype (Profunctor, Representable)
instance (forall (a :: k). Ob a => InitUniversal r a, Representable r) => Corepresentable (AsRightAdjoint (r :: j +-> k)) where
  type AsRightAdjoint r %% a = L r a
  coindex (AsRightAdjoint r) = initUnivProp r \\ r
  cotabulate f = AsRightAdjoint (rmap f initUnivArr) \\ f
  corepMap @a @b f = initUnivProp @r @a (lmap f (initUnivArr @r @b)) \\ f

newtype AsLeftAdjoint l a b = AsLeftAdjoint {unAsLeftAdjoint :: l a b}
  deriving newtype (Profunctor, Corepresentable)
instance (forall b. Ob b => TermUniversal l b, Corepresentable l) => Representable (AsLeftAdjoint l) where
  type AsLeftAdjoint l % b = R l b
  index (AsLeftAdjoint l) = termUnivProp l \\ l
  tabulate f = AsLeftAdjoint (lmap f termUnivArr) \\ f
  repMap @a @b f = termUnivProp @l @b (rmap f (termUnivArr @l @a)) \\ f

newtype FromAdjunction p a b = FromAdjunction {unFromAdjunction :: p a b}
  deriving newtype (Profunctor, Representable, Corepresentable)
instance (Adjunction p, Ob a) => InitUniversal (FromAdjunction p) a where
  type L (FromAdjunction p) a = p %% a
  initUnivArr = trivialCorep
  initUnivProp = coindex
instance (Adjunction p, Ob b) => TermUniversal (FromAdjunction p) b where
  type R (FromAdjunction p) b = p % b
  termUnivArr = trivialRep
  termUnivProp = index