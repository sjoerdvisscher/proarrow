{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Proarrow.Promonad where

import Prelude qualified as P

import Proarrow.Core (CAT, PRO, UN, Is, Category(..), Profunctor(..), type (~>), dimapDefault, lmap, rmap)
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Profunctor.Star (Star(..))
import Proarrow.Functor (Prelude(..))


class Profunctor p => Promonad p where
  unit :: Ob a => p a a
  mult :: p a b -> p b c -> p a c

instance P.Monad m => Promonad (Star (Prelude m)) where
  unit = Star (Prelude . P.pure)
  mult (Star f) (Star g) = Star \a -> Prelude (getPrelude (f a) P.>>= (getPrelude . g))


newtype KLEISLI (p :: CAT k) = KL k
type instance UN KL (KL k) = k

type Kleisli :: CAT (KLEISLI p)
data Kleisli (a :: KLEISLI p) b where
  Kleisli :: p a b -> Kleisli (KL a :: KLEISLI p) (KL b)

type instance (~>) = Kleisli

instance Promonad p => Profunctor (Kleisli :: CAT (KLEISLI p)) where
  dimap = dimapDefault
  r \\ Kleisli p = r \\ p

-- | Every promonad makes a category.
instance Promonad p => Category (Kleisli :: CAT (KLEISLI p)) where
  type Ob a = (Is KL a, Ob (UN KL a))
  id = Kleisli (unit @p)
  Kleisli f . Kleisli g = Kleisli (mult @p g f)

instance Adjunction p q => Promonad (q :.: p) where
  unit = Adj.unit
  mult (q' :.: p') (q :.: p) = rmap (Adj.counit (p' :.: q)) q' :.: p


type KleisliFree :: forall (p :: PRO k k) -> PRO (KLEISLI p) k
data KleisliFree p a b where
  KleisliFree :: p a b -> KleisliFree p (KL a) b
instance Promonad p => Profunctor (KleisliFree p) where
  dimap (Kleisli l) r (KleisliFree p) = KleisliFree (mult l (rmap r p))
  r \\ KleisliFree p = r \\ p

type KleisliForget :: forall (p :: PRO k k) -> PRO k (KLEISLI p)
data KleisliForget p a b where
  KleisliForget :: p a b -> KleisliForget p a (KL b)
instance Promonad p => Profunctor (KleisliForget p) where
  dimap l (Kleisli r) (KleisliForget p) = KleisliForget (mult (lmap l p) r)
  r \\ KleisliForget p = r \\ p

instance Promonad p => Adjunction (KleisliFree p) (KleisliForget p) where
  unit = KleisliForget unit :.: KleisliFree unit
  counit (KleisliFree p :.: KleisliForget q) = Kleisli (mult p q)