{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Monoid where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category (Supplies)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), par)
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), arr, dimapDefault, obj)
import Proarrow.Object.BinaryCoproduct (COPROD (..), Coprod (..), HasBinaryCoproducts (..), HasCoproducts, codiag)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), HasProducts, PROD (..), Prod (..), diag, (&&&))
import Proarrow.Object.Dual (CompactClosed (..), StarAutonomous (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Identity (Id (..))

type Monoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob m) => Monoid (m :: k) where
  mempty :: Unit ~> m
  mappend :: m ** m ~> m

combine :: (Monoid m) => Unit ~> m -> Unit ~> m -> Unit ~> m
combine f g = mappend . (f `par` g) . leftUnitorInv

class (Monoid m) => CommutativeMonoid (m :: k)

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

instance Comonoid '() where
  counit = id
  comult = id

instance (HasProducts k, Ob a) => Comonoid (PR (a :: k)) where
  counit = Prod terminate
  comult = Prod diag

counitAct :: forall {m} {c} (a :: m) (n :: c). (MonoidalAction m c, Comonoid a, Ob n) => Act a n ~> n
counitAct = unitor @m . act (counit @a) (obj @n)

comultAct :: forall {m} {c} (a :: m) (n :: c). (MonoidalAction m c, Comonoid a, Ob n) => Act a n ~> Act a (Act a n)
comultAct = multiplicatorInv @m @c @a @a @n . act (comult @a) (obj @n)

class (Monoidal k) => CopyDiscard k where
  copy :: (Ob (a :: k)) => a ~> a ** a
  default copy :: (k `Supplies` Comonoid) => (Ob (a :: k)) => a ~> a ** a
  copy = comult
  discard :: (Ob (a :: k)) => a ~> Unit
  default discard :: (k `Supplies` Comonoid) => (Ob (a :: k)) => a ~> Unit
  discard = counit

instance (HasProducts k) => CopyDiscard (PROD k)
instance CopyDiscard Type
instance CopyDiscard ()
instance (CopyDiscard j, CopyDiscard k) => CopyDiscard (j, k) where
  copy = copy :**: copy
  discard = discard :**: discard

type data MONOIDK (m :: k) = M
data Mon a b where
  Mon :: Unit ~> m -> Mon (M :: MONOIDK m) M
instance (Monoid m) => Profunctor (Mon :: CAT (MONOIDK m)) where
  dimap = dimapDefault
  r \\ Mon{} = r
instance (Monoid m) => Promonad (Mon :: CAT (MONOIDK m)) where
  id = Mon mempty
  Mon f . Mon g = Mon (combine f g)

-- | A monoid as a one object category.
instance (Monoid m) => CategoryOf (MONOIDK m) where
  type (~>) = Mon
  type Ob a = a P.~ M

instance (Monoid m) => HasInitialObject (MONOIDK m) where
  type InitialObject = M
  initiate = Mon mempty
instance (Monoid m) => HasTerminalObject (MONOIDK m) where
  type TerminalObject = M
  terminate = Mon mempty
instance (Monoid m) => HasBinaryProducts (MONOIDK m) where
  type a && b = M
  withObProd @M @M r = r
  fst @M @M = Mon mempty
  snd @M @M = Mon mempty
  Mon f &&& Mon g = Mon (combine f g)
instance (Monoid m) => HasBinaryCoproducts (MONOIDK m) where
  type a || b = M
  withObCoprod @M @M r = r
  lft @M @M = Mon mempty
  rgt @M @M = Mon mempty
  Mon f ||| Mon g = Mon (combine f g)

instance (CommutativeMonoid m) => MonoidalProfunctor (Mon :: CAT (MONOIDK m)) where
  par0 = Mon mempty
  Mon f `par` Mon g = Mon (combine f g)
instance (CommutativeMonoid m) => Monoidal (MONOIDK m) where
  type Unit = M
  type M ** M = M
  withOb2 r = r
  leftUnitor = Mon mempty
  leftUnitorInv = Mon mempty
  rightUnitor = Mon mempty
  rightUnitorInv = Mon mempty
  associator = Mon mempty
  associatorInv = Mon mempty
instance (CommutativeMonoid m) => SymMonoidal (MONOIDK m) where
  swap = Mon mempty

instance (CommutativeMonoid m) => StarAutonomous (MONOIDK m) where
  type Dual (M :: MONOIDK m) = M
  dual f@Mon{} = f
  dualInv f = f
  linDist _ = id
  linDistInv _ = id
instance (CommutativeMonoid m) => CompactClosed (MONOIDK m) where
  distribDual = Mon mempty
  dualUnit = Mon mempty
instance (CommutativeMonoid m) => Closed (MONOIDK m) where
  type a ~~> b = M
  withObExp r = r
  curry (Mon m) = Mon m
  apply = Mon mempty

instance (Comonoid c) => Monoid (OP c) where
  mempty = Op counit
  mappend = Op comult

instance (Monoid c) => Comonoid (OP c) where
  counit = Op mempty
  comult = Op mappend
