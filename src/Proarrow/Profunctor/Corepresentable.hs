{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Profunctor.Corepresentable where

import Data.Kind (Constraint)

import Proarrow.Category.Instance.Unit ()
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), lmap, rmap, type (+->))
import Proarrow.Functor (Copresheaf, FunctorForRep (..))
import Proarrow.Object (Obj, obj)
import Proarrow.Optic (Iso, iso)

infixl 8 %%

type Corepresentable :: forall {j} {k}. (j +-> k) -> Constraint
class (Profunctor p) => Corepresentable (p :: j +-> k) where
  type p %% (a :: k) :: j
  coindex :: p a b -> p %% a ~> b
  cotabulate :: (Ob a) => (p %% a ~> b) -> p a b
  cotabulate f = rmap f trivialCorep
  corepMap :: (a ~> b) -> p %% a ~> p %% b
  corepMap @_ @b f = coindex @p (lmap f (trivialCorep @p @b)) \\ f
  trivialCorep :: (Ob a) => p a (p %% a)
  trivialCorep @a = cotabulate (corepObj @p @a)
  {-# MINIMAL coindex, ((cotabulate, corepMap) | trivialCorep) #-}

instance Corepresentable (->) where
  type (->) %% a = a
  coindex f = f
  cotabulate f = f
  corepMap f = f
  trivialCorep = id

corepObj :: forall p a. (Corepresentable p, Ob a) => Obj (p %% a)
corepObj = corepMap @p (obj @a)

withObCorep :: forall p a r. (Corepresentable p, Ob a) => ((Ob (p %% a)) => r) -> r
withObCorep r = r \\ corepMap @p (obj @a)

dimapCorep :: forall p a b c d. (Corepresentable p) => (c ~> a) -> (b ~> d) -> p a b -> p c d
dimapCorep l r = cotabulate @p . dimap (corepMap @p l) r . coindex \\ l

cotabulated :: forall p a a' b b'. (Corepresentable p, Ob a) => Iso (p %% a ~> b) (p %% a' ~> b') (p a b) (p a' b')
cotabulated = iso cotabulate coindex

-- | A representable copresheaf is a representable functor in the Haskell sense.
type RepresentableCopresheaf (f :: Copresheaf k) = Corepresentable f

type Key (f :: Copresheaf k) = f %% '()
tabulatedCopresheaf :: (RepresentableCopresheaf f, Ob a) => Iso (Key f ~> a) (Key f ~> a') (f '() a) (f '() a')
tabulatedCopresheaf = cotabulated

type Corep :: (j +-> k) -> (k +-> j)
data Corep f a b where
  Corep :: forall f a b. (Ob a) => {unCorep :: f @ a ~> b} -> Corep f a b
instance (FunctorForRep f) => Profunctor (Corep f) where
  dimap = dimapCorep
  r \\ Corep f = r \\ f
instance (FunctorForRep f) => Corepresentable (Corep f) where
  type Corep f %% a = f @ a
  coindex (Corep f) = f
  cotabulate = Corep
  corepMap = fmap @f

corep :: forall f a b a' b'. (FunctorForRep f, Ob a) => Iso (f @ a ~> b) (f @ a' ~> b') (Corep f a b) (Corep f a' b')
corep = cotabulated

type Comonad w = (Promonad w, Corepresentable w)

extract :: forall w a. (Comonad w, Ob a) => w %% a ~> a
extract = coindex @w id

extend :: forall w a b. (Comonad w, Ob a) => (w %% a ~> b) -> (w %% a ~> w %% b)
extend f = coindex ((trivialCorep \\ f) . cotabulate @w @a f)