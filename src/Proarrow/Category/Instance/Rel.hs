{-# LANGUAGE AllowAmbiguousTypes #-}
-- Collected from https://www.clowderproject.com/tag/01D0.html
module Proarrow.Category.Instance.Rel where

import Proarrow.Adjunction (Proadjunction (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), src, (:~>), type (+->), Promonad (..))
import Proarrow.Category.Enriched.ThinCategory (Discrete, ThinProfunctor (..), withEq)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), trivialRep)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Category.Enriched.Dagger (DaggerProfunctor)

class (ThinProfunctor p, Discrete j, Discrete k) => Relation (p :: j +-> k)
instance (ThinProfunctor p, Discrete j, Discrete k) => Relation (p :: j +-> k)

type Converse :: (j +-> k) -> (k +-> j)
data Converse p a b where
  Converse :: p b a -> Converse p a b
instance (Relation p) => Profunctor (Converse p) where
  dimap f g (Converse p) = withEq f (withEq g (Converse p))
  r \\ Converse p = r \\ p
instance (Relation p) => ThinProfunctor (Converse p) where
  type HasArrow (Converse p) a b = HasArrow p b a
  arr = Converse arr
  withArr (Converse p) r = withArr p r
instance (Relation p, Representable p) => Corepresentable (Converse p) where
  type (Converse p) %% a = p % a
  coindex (Converse p) = withEq (index p) (src p)
  cotabulate f = withEq f (Converse (tabulate f))
  corepMap f = withEq f (repMap @p (src f))

asImplication
  :: forall a b p q r. (Relation p, Relation q) => p :~> q -> (Ob a, Ob b, HasArrow p a b) => ((HasArrow q a b) => r) -> r
asImplication n = withArr (n (arr @p @a @b))

class (Relation p) => Functional p where
  isFunctional :: p :.: Converse p :~> (~>)

reprIsFunctional :: (Relation p, Representable p) => p :.: Converse p :~> (~>)
reprIsFunctional (p :.: Converse p') = withEq (index p) (withEq (index p') (src p))

class (Relation p) => Total p where
  isTotal :: (~>) :~> Converse p :.: p

reprIsTotal :: (Relation p, Representable p) => (~>) :~> Converse p :.: p
reprIsTotal f = withEq f (Converse trivialRep :.: trivialRep) \\ f

class (Relation p) => Injective p where
  isInjective :: Converse p :.: p :~> (~>)

class (Relation p) => Surjective p where
  isSurjective :: (~>) :~> p :.: Converse p

class (Relation p) => Reflexive p where
  isReflexive :: (~>) :~> p

class (Relation p) => Transitive p where
  isTransitive :: p :.: p :~> p

adjToConverse :: forall p q. (Relation p, Relation q, Proadjunction p q) => q :~> Converse p
adjToConverse q = Converse (case unit @p @q of _ :.: p -> withEq (counit (p :.: q)) p) \\ q

adjFromConverse :: forall p q. (Relation p, Relation q, Proadjunction p q) => Converse p :~> q
adjFromConverse (Converse @_ @_ @a p) = (case unit @p @q @a of q :.: _ -> withEq (counit (p :.: q)) q) \\ p

class (Relation p, Promonad p) => Preorder p
instance (Relation p, Promonad p) => Preorder p

class (Relation p, DaggerProfunctor p) => Symmetric p
instance (Relation p, DaggerProfunctor p) => Symmetric p

class (Preorder p, Symmetric p) => Equivalence p
instance (Preorder p, Symmetric p) => Equivalence p