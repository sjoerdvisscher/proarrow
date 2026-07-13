module Proarrow.Universal where

import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), type (+->))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepUniv)
import Proarrow.Profunctor.Representable (Representable (..), repUniv)

-- | The initial universal property of a functor @r@ (as a representable profunctor) and an object @a@.
type InitUniversal :: forall {j} {k}. k -> (j +-> k) -> Constraint
class (Representable r, Ob a) => InitUniversal (a :: k) (r :: j +-> k) where
  type L r a :: j
  initUnivArr :: r a (L r a)
  initUnivProp :: r a b -> L r a ~> b

-- | The terminal universal property of a functor @l@ (as a corepresentable profunctor) and an object @b@.
type TermUniversal :: forall {j} {k}. j -> (j +-> k) -> Constraint
class (Corepresentable l, Ob b) => TermUniversal (b :: j) (l :: j +-> k) where
  type R l b :: k
  termUnivArr :: l (R l b) b
  termUnivProp :: l a b -> a ~> R l b

instance (TermUniversal b l) => InitUniversal (OP b) (Op l) where
  type L (Op l) (OP b) = OP (R l b)
  initUnivArr = Op termUnivArr
  initUnivProp (Op l) = Op (termUnivProp l)

instance (InitUniversal a r) => TermUniversal (OP a) (Op r) where
  type R (Op r) (OP a) = OP (L r a)
  termUnivArr = Op initUnivArr
  termUnivProp (Op l) = Op (initUnivProp l)

newtype AsRightAdjoint r a b = AsRightAdjoint {unAsRightAdjoint :: r a b}
  deriving newtype (Profunctor, Representable)
deriving newtype instance (InitUniversal a r) => InitUniversal a (AsRightAdjoint r)
instance (forall (a :: k). (Ob a) => InitUniversal a r, Representable r) => Corepresentable (AsRightAdjoint (r :: j +-> k)) where
  type AsRightAdjoint r %% a = L r a
  coindex r = initUnivProp r \\ r
  corepUniv = initUnivArr

newtype AsLeftAdjoint l a b = AsLeftAdjoint {unAsLeftAdjoint :: l a b}
  deriving newtype (Profunctor, Corepresentable)
deriving newtype instance (TermUniversal b l) => TermUniversal b (AsLeftAdjoint l)
instance (forall b. (Ob b) => TermUniversal b l, Corepresentable l) => Representable (AsLeftAdjoint l) where
  type AsLeftAdjoint l % b = R l b
  index l = termUnivProp l \\ l
  repUniv = termUnivArr

newtype FromAdjunction p a b = FromAdjunction {unFromAdjunction :: p a b}
  deriving newtype (Profunctor, Representable, Corepresentable)
instance (Adjunction p, Ob a) => InitUniversal a (FromAdjunction p) where
  type L (FromAdjunction p) a = p %% a
  initUnivArr = corepUniv
  initUnivProp = coindex
instance (Adjunction p, Ob b) => TermUniversal b (FromAdjunction p) where
  type R (FromAdjunction p) b = p % b
  termUnivArr = repUniv
  termUnivProp = index