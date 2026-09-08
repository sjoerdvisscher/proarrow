{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Corepresentable profunctors, dual to "Proarrow.Profunctor.Representable": profunctors of the shape
-- /hom preceded by a functor/, identifying @p a b@ with @p %% a ~> b@ (functorial action '%%'). 'Corep'
-- packages any 'Proarrow.Functor.FunctorForRep' as its corepresentable profunctor.
module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Category.Instance.Unit ()
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, type (+->))
import Proarrow.Functor (Copresheaf, FunctorForRep (..))
import Proarrow.Object (Obj, obj)
import Proarrow.Optic (PIso, iso)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))

infixl 8 %%

-- | A profunctor is corepresentable if @p a ?@ as a copresheaf is representable in a functorial way over @a@.
type Corepresentable :: forall {j} {k}. (j +-> k) -> Constraint
class (Profunctor p) => Corepresentable (p :: j +-> k) where
  type p %% (a :: k) :: j
  coindex :: p a b -> p %% a ~> b
  cotabulate :: (Ob a) => (p %% a ~> b) -> p a b
  cotabulate f = rmap f corepUniv
  corepMap :: (a ~> b) -> p %% a ~> p %% b
  corepMap @_ @b f = coindex @p (lmap f (corepUniv @p @b)) \\ f
  corepUniv :: (Ob a) => p a (p %% a)
  corepUniv @a = cotabulate (corepObj @p @a)
  {-# MINIMAL coindex, ((cotabulate, corepMap) | corepUniv) #-}

instance Corepresentable (->) where
  type (->) %% a = a
  coindex f = f
  cotabulate f = f
  corepMap f = f
  corepUniv = id

instance (CategoryOf k) => Corepresentable (Id :: k +-> k) where
  type Id %% a = a
  coindex = unId
  cotabulate = Id
  corepMap = id

instance (Corepresentable p, Corepresentable q) => Corepresentable (p :.: q) where
  type (p :.: q) %% a = q %% (p %% a)
  coindex (p :.: q) = coindex q . corepMap @q (coindex p)
  cotabulate :: forall a b. (Ob a) => (((p :.: q) %% a) ~> b) -> (:.:) p q a b
  cotabulate f = withObCorep @p @a (cotabulate id :.: cotabulate f)
  corepMap f = corepMap @q (corepMap @p f)

corepObj :: forall p a. (Corepresentable p, Ob a) => Obj (p %% a)
corepObj = corepMap @p (obj @a)

withObCorep :: forall p a r. (Corepresentable p, Ob a) => ((Ob (p %% a)) => r) -> r
withObCorep r = r \\ corepMap @p (obj @a)

dimapCorep :: forall p a b c d. (Corepresentable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapCorep l r = cotabulate @p . dimap (corepMap @p l) r . coindex \\ l

cotabulated :: forall p a a' b b'. (Corepresentable p, Ob a) => PIso (p %% a ~> b) (p %% a' ~> b') (p a b) (p a' b')
cotabulated = iso cotabulate coindex

-- | A representable copresheaf is a representable functor in the Haskell sense.
type RepresentableCopresheaf (f :: Copresheaf k) = Corepresentable f

type Key (f :: Copresheaf k) = f %% '()
tabulatedCopresheaf :: (RepresentableCopresheaf f, Ob a) => PIso (Key f ~> a) (Key f ~> a') (f '() a) (f '() a')
tabulatedCopresheaf = cotabulated

-- | Dual to 'Proarrow.Profunctor.Representable.Rep': the corepresentable profunctor of @f@, a
-- value @'Corep' f a b@ being an arrow @f \@ a '~>' b@.
type Corep :: (j +-> k) -> (k +-> j)
data Corep f a b where
  Corep :: forall a f b. (Ob a) => {unCorep :: f @ a ~> b} -> Corep f a b

instance (FunctorForRep f) => Profunctor (Corep f) where
  dimap = dimapCorep
  r \\ Corep f = r \\ f
instance (FunctorForRep f) => Corepresentable (Corep f) where
  type Corep f %% a = f @ a
  coindex (Corep f) = f
  cotabulate = Corep
  corepMap = fmap @f

corep :: forall f a b a' b'. (FunctorForRep f, Ob a) => PIso (f @ a ~> b) (f @ a' ~> b') (Corep f a b) (Corep f a' b')
corep = cotabulated
