{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Kleisli
  ( KLEISLI (..)
  , Kleisli (..)
  , arr
  , KleisliFree (..)
  , KleisliForget (..)
  , LIFTEDF
  , pattern LiftF
  ) where

import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Category.Monoidal.Distributive (Distributive (..), DistributiveProfunctor)
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Is
  , Profunctor (..)
  , Promonad (..)
  , UN
  , dimapDefault
  , lmap
  , rmap
  , type (+->)
  )
import Proarrow.Functor (Functor)
import Proarrow.Object (pattern Obj, type Obj)
import Proarrow.Object.BinaryCoproduct (Coprod, HasBinaryCoproducts (..), codiag, copar)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), diag)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Costar (Costar (..))
import Proarrow.Profunctor.Star (Star (..))

newtype KLEISLI (p :: CAT k) = KL k
type instance UN KL (KL k) = k -- test

type Kleisli :: CAT (KLEISLI p)
data Kleisli (a :: KLEISLI p) b where
  Kleisli :: {runKleisli :: p a b} -> Kleisli (KL a :: KLEISLI p) (KL b)

instance (Promonad p) => Profunctor (Kleisli :: CAT (KLEISLI p)) where
  dimap = dimapDefault
  r \\ Kleisli p = r \\ p

arr :: (Promonad p) => a ~> b -> Kleisli (KL a :: KLEISLI p) (KL b)
arr f = Kleisli (rmap f id) \\ f

-- | Every promonad makes a category.
instance (Promonad p) => CategoryOf (KLEISLI p) where
  type (~>) = Kleisli
  type Ob a = (Is KL a, Ob (UN KL a))

instance (Promonad p) => Promonad (Kleisli :: CAT (KLEISLI p)) where
  id = Kleisli id
  Kleisli f . Kleisli g = Kleisli (f . g)

instance (HasTerminalObject k, Promonad p) => HasTerminalObject (KLEISLI (p :: k +-> k)) where
  type TerminalObject @(KLEISLI (p :: k +-> k)) = KL (TerminalObject :: k)
  terminate = arr terminate

instance (HasInitialObject k, Promonad p) => HasInitialObject (KLEISLI (p :: k +-> k)) where
  type InitialObject @(KLEISLI (p :: k +-> k)) = KL (InitialObject :: k)
  initiate = arr initiate

instance (Cartesian k, Promonad p, MonoidalProfunctor p) => HasBinaryProducts (KLEISLI (p :: k +-> k)) where
  type a && b = KL (UN KL a && UN KL b)
  withObProd @(KL a) @(KL b) r = withObProd @k @a @b r
  fst @(KL a) @(KL b) = arr (fst @_ @a @b)
  snd @(KL a) @(KL b) = arr (snd @_ @a @b)
  Kleisli f &&& Kleisli g = Kleisli (lmap diag (f `par` g)) \\ f

instance (HasBinaryCoproducts k, Promonad p, MonoidalProfunctor (Coprod p)) => HasBinaryCoproducts (KLEISLI (p :: k +-> k)) where
  type a || b = KL (UN KL a || UN KL b)
  withObCoprod @(KL a) @(KL b) r = withObCoprod @k @a @b r
  lft @(KL a) @(KL b) = arr (lft @_ @a @b)
  rgt @(KL a) @(KL b) = arr (rgt @_ @a @b)
  Kleisli f ||| Kleisli g = Kleisli (rmap codiag (f `copar` g)) \\ f

instance (Promonad p, MonoidalProfunctor p) => MonoidalProfunctor (Kleisli :: CAT (KLEISLI (p :: k +-> k))) where
  par0 = Kleisli par0
  Kleisli f `par` Kleisli g = Kleisli (f `par` g)

instance (Promonad p, MonoidalProfunctor p) => Monoidal (KLEISLI (p :: k +-> k)) where
  type Unit @(KLEISLI (p :: k +-> k)) = KL (Unit :: k)
  type a ** b = KL (UN KL a ** UN KL b)
  withOb2 @(KL a) @(KL b) = withOb2 @k @a @b
  leftUnitor = arr leftUnitor
  leftUnitorInv = arr leftUnitorInv
  rightUnitor = arr rightUnitor
  rightUnitorInv = arr rightUnitorInv
  associator @(KL a) @(KL b) @(KL c) = arr (associator @k @a @b @c)
  associatorInv @(KL a) @(KL b) @(KL c) = arr (associatorInv @k @a @b @c)
instance (Promonad p, MonoidalProfunctor p, SymMonoidal k) => SymMonoidal (KLEISLI (p :: k +-> k)) where
  swap @(KL a) @(KL b) = arr (swap @k @a @b)

instance (Distributive k, Promonad p, DistributiveProfunctor p) => Distributive (KLEISLI (p :: k +-> k)) where
  distL @(KL a) @(KL b) @(KL c) = arr (distL @k @a @b @c)
  distR @(KL a) @(KL b) @(KL c) = arr (distR @k @a @b @c)
  distL0 @(KL a) = arr (distL0 @k @a)
  distR0 @(KL a) = arr (distR0 @k @a)

instance (Strong k p, Promonad p, Monoidal k) => Strong k (Kleisli :: CAT (KLEISLI (p :: k +-> k))) where
  act f (Kleisli p) = Kleisli (act f p)
instance (Strong k p, Promonad p, Monoidal k) => MonoidalAction k (KLEISLI (p :: k +-> k)) where
  type Act y (KL x) = KL (Act y x)
  withObAct @y @(KL x) r = withObAct @k @k @y @x r
  unitor = arr (unitor @k)
  unitorInv = arr (unitorInv @k)
  multiplicator @a @b @(KL c) = arr (multiplicator @k @k @a @b @c)
  multiplicatorInv @a @b @(KL c) = arr (multiplicatorInv @k @k @a @b @c)

type KleisliFree :: forall (p :: k +-> k) -> k +-> KLEISLI p
data KleisliFree p a b where
  KleisliFree :: p a b -> KleisliFree p (KL a) b
instance (Promonad p) => Profunctor (KleisliFree p) where
  dimap (Kleisli l) r (KleisliFree p) = KleisliFree (rmap r p . l)
  r \\ KleisliFree p = r \\ p

type KleisliForget :: forall (p :: k +-> k) -> KLEISLI p +-> k
data KleisliForget p a b where
  KleisliForget :: p a b -> KleisliForget p a (KL b)
instance (Promonad p) => Profunctor (KleisliForget p) where
  dimap l (Kleisli r) (KleisliForget p) = KleisliForget (r . lmap l p)
  r \\ KleisliForget p = r \\ p

instance (Promonad p) => Adjunction (KleisliFree p) (KleisliForget p) where
  unit = KleisliForget id :.: KleisliFree id
  counit (KleisliFree p :.: KleisliForget q) = Kleisli (q . p)

-- | Categories lifted by a functor: @f a ~> f b@.
type LIFTEDF (f :: j -> k) = KLEISLI (Costar f :.: Star f)

unlift :: (Functor f) => Kleisli (KL a :: LIFTEDF f) (KL b) -> (f a ~> f b, Obj a, Obj b)
unlift (Kleisli (Costar f :.: Star g)) = (g . f, Obj, Obj)

pattern LiftF :: (Functor f) => (Ob a, Ob b) => (f a ~> f b) -> Kleisli (KL a :: LIFTEDF f) (KL b)
pattern LiftF f <- (unlift -> (f, Obj, Obj))
  where
    LiftF f = Kleisli (Costar f :.: Star id)

{-# COMPLETE LiftF #-}