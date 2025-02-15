{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Kleisli where

import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
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
  , tgt
  , type (+->)
  )
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..), codiag)
import Proarrow.Object.BinaryProduct
  ( HasBinaryProducts (..)
  , PROD (..)
  , Prod (..)
  , StrongProd
  , associatorProd
  , associatorProdInv
  , diag
  , first'
  , leftUnitorProd
  , leftUnitorProdInv
  , rightUnitorProd
  , rightUnitorProdInv
  , second'
  , swapProd'
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

-- | This is not monoidal but premonoidal, i.e. no sliding.
-- So with `par f g` the effects of f happen before the effects of g.
instance (Promonad p, StrongProd p) => MonoidalProfunctor (Kleisli :: CAT (KLEISLI (p :: k +-> k))) where
  par0 = Kleisli id
  Kleisli @_ @_ @b1 f `par` Kleisli @_ @a2 @_ g = Kleisli (second' @_ @b1 g . first' @_ @a2 f) \\ f \\ g

instance (Promonad p, StrongProd p) => Monoidal (KLEISLI (p :: k +-> k)) where
  type Unit @(KLEISLI (p :: k +-> k)) = KL (TerminalObject :: k)
  type a ** b = KL (UN KL a && UN KL b)
  leftUnitor = arr leftUnitorProd
  leftUnitorInv = arr leftUnitorProdInv
  rightUnitor = arr rightUnitorProd
  rightUnitorInv = arr rightUnitorProdInv
  associator @(KL a) @(KL b) @(KL c) = arr (associatorProd @a @b @c)
  associatorInv @(KL a) @(KL b) @(KL c) = arr (associatorProdInv @a @b @c)
instance (Promonad p, StrongProd p) => SymMonoidal (KLEISLI (p :: k +-> k)) where
  swap' l@(Kleisli pl) r@(Kleisli pr) = arr (swapProd' (tgt pl) (tgt pr)) . (l `par` r)

instance (Strong k p, Promonad p, Monoidal k) => Strong k (Kleisli :: CAT (KLEISLI (p :: k +-> k))) where
  act f (Kleisli p) = Kleisli (act f p)
instance (Strong k p, Promonad p, Monoidal k) => MonoidalAction k (KLEISLI (p :: k +-> k)) where
  type Act y (KL x) = KL (Act y x)
  unitor = arr (unitor @k)
  unitorInv = arr (unitorInv @k)
  multiplicator @a @b @(KL c) = arr (multiplicator @k @k @a @b @c)
  multiplicatorInv @a @b @(KL c) = arr (multiplicatorInv @k @k @a @b @c)

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