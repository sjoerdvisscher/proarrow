{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Proarrow.Category.Instance.Kleisli where

import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Core (CAT, CategoryOf (..), Is, type (+->), Profunctor (..), Promonad (..), UN, dimapDefault, lmap, rmap, src, tgt)
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Object.BinaryProduct (HasProducts, HasBinaryProducts(..), leftUnitorProd, leftUnitorProdInv, rightUnitorProd, rightUnitorProdInv, associatorProd, associatorProdInv, swapProd, PROD (..), Prod (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..), Monoidal (..))
import Proarrow.Category.Monoidal.Distributive (Distributive(..))
import Proarrow.Object.Terminal (HasTerminalObject(..))
import Proarrow.Object.BinaryCoproduct (HasCoproducts, HasBinaryCoproducts (..), codiag)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Exponential (BiCCC)

newtype KLEISLI (p :: CAT k) = KL k
type instance UN KL (KL k) = k

type Kleisli :: CAT (KLEISLI p)
data Kleisli (a :: KLEISLI p) b where
  Kleisli :: p a b -> Kleisli (KL a :: KLEISLI p) (KL b)

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

instance (HasCoproducts k, Promonad p) => HasInitialObject (KLEISLI (p :: k +-> k)) where
  type InitialObject = KL InitialObject
  initiate = arr initiate

instance (HasCoproducts k, Promonad p, Costrong p) => HasBinaryCoproducts (KLEISLI (p :: k +-> k)) where
  type a || b = KL (UN KL a || UN KL b)
  lft @(KL a) @(KL b) = arr (lft @_ @a @b)
  rgt @(KL a) @(KL b) = arr (rgt @_ @a @b)
  Kleisli @_ @_ @b1 f ||| Kleisli @_ @a2 @_ g = arr codiag . Kleisli (right b1 g . left a2 f) \\ f \\ g

class (HasBinaryProducts k, Profunctor p) => Strong (p :: k +-> k) where
  first :: Ob c => p a b -> p (a && c) (b && c)
  second :: Ob c => p a b -> p (c && a) (c && b)
  second @c @a @b p = dimap (swapProd @_ @c @a) (swapProd @_ @b @c) (first @_ @_ @c p) \\ p

class (HasBinaryCoproducts k, Profunctor p) => Costrong (p :: k +-> k) where
  left :: forall c -> Ob c => p a b -> p (a || c) (b || c)
  right :: forall c -> Ob c => p a b -> p (c || a) (c || b)
  -- right @a @b c p = dimap (swapCoprod @_ @c @a) (swapCoprod @_ @b @c) (left c p) \\ p

-- | This is not monoidal but premonoidal, i.e. no sliding.
-- So with `par f g` the effects of f happen before the effects of g.
instance (HasProducts k, Promonad p, Strong p) => MonoidalProfunctor (Kleisli :: CAT (KLEISLI (p :: k +-> k))) where
  par0 = Kleisli id
  Kleisli @_ @_ @b1 f `par` Kleisli @_ @a2 @_ g = Kleisli (second @_ @_ @b1 g . first @_ @_ @a2 f) \\ f \\ g

instance (HasProducts k, Promonad p, Strong p) => Monoidal (KLEISLI (p :: k +-> k)) where
  type Unit @(KLEISLI (p :: k +-> k)) = KL (TerminalObject :: k)
  type a ** b = KL (UN KL a && UN KL b)
  leftUnitor (Kleisli p) = Kleisli (lmap (leftUnitorProd (src p)) p)
  leftUnitorInv (Kleisli p) = Kleisli (rmap (leftUnitorProdInv (tgt p)) p)
  rightUnitor (Kleisli p) = Kleisli (lmap (rightUnitorProd (src p)) p)
  rightUnitorInv (Kleisli p) = Kleisli (rmap (rightUnitorProdInv (tgt p)) p)
  associator (Kleisli a) (Kleisli b) (Kleisli c) = arr (associatorProd (src a) (src b) (src c))
  associatorInv (Kleisli a) (Kleisli b) (Kleisli c) = arr (associatorProdInv (src a) (src b) (src c))

instance (BiCCC k, Promonad p, Strong p, Costrong p) => Distributive (KLEISLI (p :: k +-> k)) where
  distL0 @(KL a) = arr (snd @_ @a)
  distR0 @(KL a) = arr (fst @_ @_ @a)
  distL @(KL a) @(KL b) @(KL c) = arr (unProd (distL @_ @(PR a) @(PR b) @(PR c)))
  distR @(KL a) @(KL b) @(KL c) = arr (unProd (distR @_ @(PR a) @(PR b) @(PR c)))
