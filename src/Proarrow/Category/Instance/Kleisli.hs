{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Kleisli where

import Data.Kind (Constraint)

import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Distributive (distL)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
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
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), codiag, swapCoprod)
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , HasProducts
  , PROD (..)
  , Prod (..)
  , associatorProd
  , associatorProdInv
  , diag
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , swapProd
  )
import Proarrow.Object.Exponential (BiCCC)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Composition ((:.:) (..))

newtype KLEISLI (p :: CAT k) = KL k
type instance UN KL (KL k) = k

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
  id = Kleisli (id @p)
  Kleisli f . Kleisli g = Kleisli (f . g)

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

type Strong :: forall {k}. CAT k -> Constraint
class (HasBinaryProducts k, Profunctor p) => Strong (p :: k +-> k) where
  first :: (Ob c) => p a b -> p (a && c) (b && c)
  second :: (Ob c) => p a b -> p (c && a) (c && b)
  second @c @a @b p = dimap (swapProd @_ @c @a) (swapProd @_ @b @c) (first @_ @c p) \\ p

instance (Costrong p) => Strong (Op p) where
  first @(OP c) (Op p) = Op (left @_ @c p)
  second @(OP c) (Op p) = Op (right @_ @c p)

type Costrong :: forall {k}. CAT k -> Constraint
class (HasBinaryCoproducts k, Profunctor p) => Costrong (p :: k +-> k) where
  left :: (Ob c) => p a b -> p (a || c) (b || c)
  right :: (Ob c) => p a b -> p (c || a) (c || b)
  right @c @a @b p = dimap (swapCoprod @_ @c @a) (swapCoprod @_ @b @c) (left @_ @c p) \\ p

instance (Strong p) => Costrong (Op p) where
  left @(OP c) (Op p) = Op (first @_ @c p)
  right @(OP c) (Op p) = Op (second @_ @c p)

-- | This is not monoidal but premonoidal, i.e. no sliding.
-- So with `par f g` the effects of f happen before the effects of g.
instance (HasProducts k, Promonad p, Strong p) => MonoidalProfunctor (Kleisli :: CAT (KLEISLI (p :: k +-> k))) where
  par0 = Kleisli id
  Kleisli @_ @_ @b1 f `par` Kleisli @_ @a2 @_ g = Kleisli (second @_ @b1 g . first @_ @a2 f) \\ f \\ g

instance (HasProducts k, Promonad p, Strong p) => Monoidal (KLEISLI (p :: k +-> k)) where
  type Unit @(KLEISLI (p :: k +-> k)) = KL (TerminalObject :: k)
  type a ** b = KL (UN KL a && UN KL b)
  leftUnitor = arr leftUnitorProd
  leftUnitorInv = arr leftUnitorProdInv
  rightUnitor = arr rightUnitorProd
  rightUnitorInv = arr rightUnitorProdInv
  associator @(KL a) @(KL b) @(KL c) = arr (associatorProd @a @b @c)
  associatorInv @(KL a) @(KL b) @(KL c) = arr (associatorProdInv @a @b @c)

type DUAL (a :: KLEISLI p) = KL (OP (UN KL a)) :: KLEISLI (Op p)
type UNDUAL (a :: KLEISLI (Op p)) = KL (UN OP (UN KL a)) :: KLEISLI p
type (++) :: forall {k} {p}. KLEISLI (p :: k +-> k) -> KLEISLI p -> KLEISLI p
type (a :: KLEISLI p) ++ b = UNDUAL (DUAL a ** DUAL b)

dual :: a ~> b -> DUAL b ~> DUAL a
dual (Kleisli p) = Kleisli (Op p)

dist
  :: forall {k} {p} a b c
   . (BiCCC k, Promonad p, Ob (a :: KLEISLI (p :: k +-> k)), Ob b, Ob c)
  => (a ** (b ++ c)) ~> ((a ** b) ++ (a ** c))
dist @(KL a') @(KL b') @(KL c') = arr (unProd (distL @_ @(PR a') @(PR b') @(PR c')))

copy :: (HasBinaryProducts k, Promonad p, Ob (a :: KLEISLI (p :: k +-> k))) => a ~> (a ** a)
copy = arr diag

discard :: (HasTerminalObject k, Promonad p, Ob (a :: KLEISLI (p :: k +-> k))) => a ~> Unit
discard = arr terminate

add :: (HasBinaryCoproducts k, Promonad p, Ob (a :: KLEISLI (p :: k +-> k))) => (a ++ a) ~> a
add = arr codiag

zero :: (HasInitialObject k, Promonad p, Ob (a :: KLEISLI (p :: k +-> k))) => UNDUAL Unit ~> a
zero = arr initiate