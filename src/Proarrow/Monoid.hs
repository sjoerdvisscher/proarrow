{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Monoid where

import Data.Kind (Constraint, Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), (**))
import Proarrow.Category.Monoidal.Action (Act, MonoidalAction (..), actHom)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Colimit.BinaryCoproduct
  ( COPROD (..)
  , Coprod (..)
  , HasBinaryCoproducts (..)
  , HasBiproducts (..)
  , HasCoproducts
  , codiag
  )
import Proarrow.Colimit.Initial (HasInitialObject (..), HasZeroObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), arr, dimapDefault, obj, type (+->))
import Proarrow.Limit.BinaryProduct (Cartesian, HasBinaryProducts (..), HasProducts, PROD (..), Prod (..), diag, (&&&))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Representable (Rep (..))

type Monoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob m) => Monoid (m :: k) where
  mempty :: Unit ~> m
  mappend :: m ** m ~> m

combine :: (Monoid m) => Unit ~> m -> Unit ~> m -> Unit ~> m
combine f g = mappend . (f ** g) . leftUnitorInv

memptyS :: (Monoid m) => '[] ~> '[m]
memptyS = Str mempty

mappendS :: (Monoid m) => '[m, m] ~> '[m]
mappendS = Str mappend

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

memptyAct :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Monoid a, Ob n) => n ~> Act t a n
memptyAct = actHom @t (mempty @a) (obj @n) . unitorInv @t

mappendAct
  :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Monoid a, Ob n) => Act t a (Act t a n) ~> Act t a n
mappendAct = actHom @t (mappend @a) (obj @n) . multiplicatorInv @t @a @a @n

type Comonoid :: forall {k}. k -> Constraint
class (Monoidal k, Ob c) => Comonoid (c :: k) where
  counit :: c ~> Unit
  comult :: c ~> c ** c

counitS :: (Comonoid c) => '[c] ~> '[]
counitS = Str counit

comultS :: (Comonoid c) => '[c] ~> '[c, c]
comultS = Str comult

instance Comonoid (a :: Type) where
  counit _ = ()
  comult a = (a, a)

instance Comonoid '() where
  counit = id
  comult = id

instance (HasProducts k, Ob a) => Comonoid (PR (a :: k)) where
  counit = Prod terminate
  comult = Prod diag

counitAct :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Comonoid a, Ob n) => Act t a n ~> n
counitAct = unitor @t . actHom @t (counit @a) (obj @n)

comultAct
  :: forall {m} {c} t (a :: m) (n :: c). (MonoidalAction t, Comonoid a, Ob n) => Act t a n ~> Act t a (Act t a n)
comultAct = multiplicator @t @a @a @n . actHom @t (comult @a) (obj @n)

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
  one = Mon mempty
  Mon f ** Mon g = Mon (combine f g)
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

instance (HasZeroObject k, HasBiproducts k, Ob (a :: k), Ob b) => P.Semigroup (Id a b) where
  Id f <> Id g = Id (sum f g)
instance (HasZeroObject k, HasBiproducts k, Ob (a :: k), Ob b) => P.Monoid (Id a b) where
  mempty = Id zero
instance (HasZeroObject k, HasBiproducts k, Ob (a :: k), Ob b) => CommutativeMonoid (Id a b)

instance (Monoidal k, Monoid r) => MonoidalProfunctor (Rep (Constant r) :: k +-> k) where
  one = Rep mempty
  Rep @x l ** Rep @y r = withOb2 @k @x @y (Rep (mappend . (l ** r)))
instance (HasCoproducts k, Ob r) => MonoidalProfunctor (Coprod (Rep (Constant r)) :: COPROD k +-> COPROD k) where
  one = Coprod (Rep initiate)
  Coprod @_ @_ @x (Rep l) ** Coprod @_ @_ @y (Rep r) = withObCoprod @k @x @y (Coprod (Rep (l ||| r)))
instance (Monoidal k, Comonoid r) => MonoidalProfunctor (Corep (Constant r) :: k +-> k) where
  one = Corep counit
  Corep @x l ** Corep @y r = withOb2 @k @x @y (Corep ((l ** r) . comult))
