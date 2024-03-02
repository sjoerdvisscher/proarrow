{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Instance.Kleisli where

import Proarrow.Core (CAT, PRO, UN, Is, CategoryOf(..), Promonad(..), Profunctor(..), dimapDefault, lmap, rmap)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj


newtype KLEISLI (p :: CAT k) = KL k
type instance UN KL (KL k) = k

type Kleisli :: CAT (KLEISLI p)
data Kleisli (a :: KLEISLI p) b where
  Kleisli :: p a b -> Kleisli (KL a :: KLEISLI p) (KL b)

instance Promonad p => Profunctor (Kleisli :: CAT (KLEISLI p)) where
  dimap = dimapDefault
  r \\ Kleisli p = r \\ p

-- | Every promonad makes a category.
instance Promonad p => CategoryOf (KLEISLI p) where
  type (~>) = Kleisli
  type Ob a = (Is KL a, Ob (UN KL a))

instance Promonad p => Promonad (Kleisli :: CAT (KLEISLI p)) where
  id = Kleisli (id @p)
  Kleisli f . Kleisli g = Kleisli (f . g)


type KleisliFree :: forall (p :: PRO k k) -> PRO (KLEISLI p) k
data KleisliFree p a b where
  KleisliFree :: p a b -> KleisliFree p (KL a) b
instance Promonad p => Profunctor (KleisliFree p) where
  dimap (Kleisli l) r (KleisliFree p) = KleisliFree (rmap r p . l)
  r \\ KleisliFree p = r \\ p

type KleisliForget :: forall (p :: PRO k k) -> PRO k (KLEISLI p)
data KleisliForget p a b where
  KleisliForget :: p a b -> KleisliForget p a (KL b)
instance Promonad p => Profunctor (KleisliForget p) where
  dimap l (Kleisli r) (KleisliForget p) = KleisliForget (r . lmap l p)
  r \\ KleisliForget p = r \\ p

instance Promonad p => Adjunction (KleisliFree p) (KleisliForget p) where
  unit = KleisliForget id :.: KleisliFree id
  counit (KleisliFree p :.: KleisliForget q) = Kleisli (q . p)