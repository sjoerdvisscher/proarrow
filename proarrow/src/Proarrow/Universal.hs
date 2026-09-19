-- | Universal properties of a functor at a single object: 'InitUniversal' @a r@ gives the universal
-- arrow from @a@ to the functor @r@, 'TermUniversal' dually. The 'AsRightAdjoint'\/'AsLeftAdjoint'
-- newtypes upgrade a functor with a universal property at /every/ object to a full
-- 'Proarrow.Adjunction.Adjunction'.
module Proarrow.Universal where

import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), type (+->))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepUniv)
import Proarrow.Profunctor.Representable (Representable (..), repUniv)

-- | The initial universal property of a functor @r@ (as a representable profunctor) and an object @a@.
type InitUniversal :: forall {j} {k}. k -> (j +-> k) -> Constraint
class (Representable r, Ob a) => InitUniversal (a :: k) (r :: j +-> k) where
  -- | The target of the universal arrow out of @a@.
  type InitUnivTgt r a :: j

  initUnivArr :: r a (InitUnivTgt r a)
  initUnivProp :: r a b -> InitUnivTgt r a ~> b

-- | The terminal universal property of a functor @l@ (as a corepresentable profunctor) and an object @b@.
type TermUniversal :: forall {j} {k}. j -> (j +-> k) -> Constraint
class (Corepresentable l, Ob b) => TermUniversal (b :: j) (l :: j +-> k) where
  -- | The source of the universal arrow into @b@.
  type TermUnivSrc l b :: k

  termUnivArr :: l (TermUnivSrc l b) b
  termUnivProp :: l a b -> a ~> TermUnivSrc l b

instance (TermUniversal b l) => InitUniversal (OP b) (Op l) where
  type InitUnivTgt (Op l) (OP b) = OP (TermUnivSrc l b)
  initUnivArr = Op termUnivArr
  initUnivProp (Op l) = Op (termUnivProp l)

instance (InitUniversal a r) => TermUniversal (OP a) (Op r) where
  type TermUnivSrc (Op r) (OP a) = OP (InitUnivTgt r a)
  termUnivArr = Op initUnivArr
  termUnivProp (Op l) = Op (initUnivProp l)

newtype AsRightAdjoint r a b = AsRightAdjoint {unAsRightAdjoint :: r a b}
  deriving newtype (Profunctor, Representable)
deriving newtype instance (InitUniversal a r) => InitUniversal a (AsRightAdjoint r)
instance (forall (a :: k). (Ob a) => InitUniversal a r, Representable r) => Corepresentable (AsRightAdjoint (r :: j +-> k)) where
  type AsRightAdjoint r %% a = InitUnivTgt r a
  coindex r = initUnivProp r \\ r
  corepUniv = initUnivArr

newtype AsLeftAdjoint l a b = AsLeftAdjoint {unAsLeftAdjoint :: l a b}
  deriving newtype (Profunctor, Corepresentable)
deriving newtype instance (TermUniversal b l) => TermUniversal b (AsLeftAdjoint l)
instance (forall b. (Ob b) => TermUniversal b l, Corepresentable l) => Representable (AsLeftAdjoint l) where
  type AsLeftAdjoint l % b = TermUnivSrc l b
  index l = termUnivProp l \\ l
  repUniv = termUnivArr

newtype FromAdjunction p a b = FromAdjunction {unFromAdjunction :: p a b}
  deriving newtype (Profunctor, Representable, Corepresentable)
instance (Adjunction p, Ob a) => InitUniversal a (FromAdjunction p) where
  type InitUnivTgt (FromAdjunction p) a = p %% a
  initUnivArr = corepUniv
  initUnivProp = coindex
instance (Adjunction p, Ob b) => TermUniversal b (FromAdjunction p) where
  type TermUnivSrc (FromAdjunction p) b = p % b
  termUnivArr = repUniv
  termUnivProp = index
