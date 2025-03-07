{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Monoid where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Monoidal (Monoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), arr, obj)
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..), HasCoproducts, codiag)
import Proarrow.Object.BinaryProduct (Cartesian, HasProducts, PROD (..), Prod (..), diag, (&&&))
import Proarrow.Object.Initial (initiate)
import Proarrow.Object.Terminal (terminate)
import Proarrow.Profunctor.Identity (Id(..))

type Monoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob m) => Monoid (m :: k) where
  mempty :: Unit ~> m
  mappend :: m ** m ~> m

instance (P.Monoid m) => Monoid (m :: Type) where
  mempty () = P.mempty
  mappend = P.uncurry (P.<>)

newtype GenElt x m = GenElt (x ~> m)

instance (Monoid m, Cartesian k) => P.Semigroup (GenElt x (m :: k)) where
  GenElt f <> GenElt g = GenElt (mappend . (f &&& g))
instance (Monoid m, Cartesian k, Ob x) => P.Monoid (GenElt x (m :: k)) where
  mempty = GenElt (mempty . arr terminate)

instance (HasCoproducts k, Ob a) => Monoid (COPR (a :: k)) where
  mempty = Coprod (Id initiate)
  mappend = Coprod (Id codiag)

memptyAct :: forall {m} {c} (a :: m) (n :: c). (MonoidalAction m c, Monoid a, Ob n) => n ~> Act a n
memptyAct = act (mempty @a) (obj @n) . unitorInv @m

mappendAct :: forall {m} {c} (a :: m) (n :: c). (MonoidalAction m c, Monoid a, Ob n) => Act a (Act a n) ~> Act a n
mappendAct = act (mappend @a) (obj @n) . multiplicator @m @c @a @a @n

type ModuleObject :: forall {m} {c}. m -> c -> Constraint
class (MonoidalAction m c, Monoid a, Ob n) => ModuleObject (a :: m) (n :: c) where
  action :: Act a n ~> n

type Comonoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob c) => Comonoid (c :: k) where
  counit :: c ~> Unit
  comult :: c ~> c ** c

instance Comonoid (a :: Type) where
  counit _ = ()
  comult a = (a, a)

instance (HasProducts k, Ob a) => Comonoid (PR (a :: k)) where
  counit = Prod terminate
  comult = Prod diag

counitAct :: forall {m} {c} (a :: m) (n :: c). (MonoidalAction m c, Comonoid a, Ob n) => Act a n ~> n
counitAct = unitor @m . act (counit @a) (obj @n)

comultAct :: forall {m} {c} (a :: m) (n :: c). (MonoidalAction m c, Comonoid a, Ob n) => Act a n ~> Act a (Act a n)
comultAct = multiplicatorInv @m @c @a @a @n . act (comult @a) (obj @n)