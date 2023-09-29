module Proarrow.Promonad where

import Proarrow.Core (CAT, PRO, Category(..), Profunctor(..), type (~>), dimapDefault, lmap, rmap, CategoryOf)
import Proarrow.Profunctor.Composition ((:.:)(..), Compose)
import Proarrow.Adjunction (Adjunction)
import Proarrow.Adjunction qualified as Adj
import Proarrow.Monoid qualified as Mon
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Identity (Id(..))

class Profunctor p => Promonad p where
  unit :: Ob a => p a a
  mult :: p a b -> p b c -> p a c

newtype KLEISLI (p :: CAT k) = KL { unKL :: k }
-- can't use unKL at the type level
type family UNKL (a :: KLEISLI p) where UNKL (KL k) = k

type Kleisli :: CAT (KLEISLI p)
data Kleisli (a :: KLEISLI p) b where
  Kleisli :: p a b -> Kleisli (KL a :: KLEISLI p) (KL b)

type instance (~>) = Kleisli

instance Promonad p => Profunctor (Kleisli :: CAT (KLEISLI p)) where
  dimap = dimapDefault
  r \\ Kleisli p = r \\ p

-- | Every promonad makes a category.
instance Promonad p => Category (Kleisli :: CAT (KLEISLI p)) where
  type Ob a = (a ~ KL (UNKL a), Ob (UNKL a))
  id = Kleisli (unit @p)
  Kleisli f . Kleisli g = Kleisli (mult @p g f)

instance Adjunction p q => Promonad (q :.: p) where
  unit = Adj.unit
  mult (q' :.: p') (q :.: p) = rmap (Adj.counit (p' :.: q)) q' :.: p

instance CategoryOf k => Mon.Monoid (Promonad p) (p :: PRO k k) where
  type Ten (Promonad p) = Compose
  unit = Prof \(Id f) -> rmap f unit \\ f
  mult = Prof \(p :.: q) -> mult p q


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