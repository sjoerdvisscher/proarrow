module Proarrow.Category.Instance.Coproduct where

import Data.Kind (Constraint)

import Proarrow.Core (CategoryOf (..), type (+->), Profunctor, Promonad)
import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow (Profunctor(..))
import Proarrow.Promonad (Promonad(..))

type data COPRODUCT j k = L j | R k

type (:++:) :: (j1 +-> k1) -> (j2 +-> k2) -> COPRODUCT j1 j2 +-> COPRODUCT k1 k2
data (:++:) p q a b where
  InjL :: p a b -> (p :++: q) (L a) (L b)
  InjR :: q a b -> (p :++: q) (R a) (R b)

type IsLR :: forall {j} {k}. COPRODUCT j k -> Constraint
class IsLR (a :: COPRODUCT j k) where
  lrId :: (Promonad p, Promonad q) => (p :++: q) a a
instance (Ob a) => IsLR (L a :: COPRODUCT j k) where
  lrId = InjL id
instance (Ob a) => IsLR (R a :: COPRODUCT j k) where
  lrId = InjR id

instance (Profunctor p, Profunctor q) => Profunctor (p :++: q) where
  dimap (InjL f) (InjL g) (InjL p) = InjL (dimap f g p)
  dimap (InjR f) (InjR g) (InjR q) = InjR (dimap f g q)
  dimap InjL{} InjR{} p = case p of
  dimap InjR{} InjL{} q = case q of
  r \\ InjL p = r \\ p
  r \\ InjR q = r \\ q
-- | The coproduct of two promonads.
instance (Promonad p, Promonad q) => Promonad (p :++: q) where
  id = lrId
  InjL p . InjL q = InjL (p . q)
  InjR q . InjR r = InjR (q . r)
-- | The coproduct of two categories.
instance (CategoryOf j, CategoryOf k) => CategoryOf (COPRODUCT j k) where
  type (~>) @(COPRODUCT j k) = (~>) @j :++: (~>) @k
  type Ob (a :: COPRODUCT j k) = IsLR a

instance (DaggerProfunctor p, DaggerProfunctor q) => DaggerProfunctor (p :++: q) where
  dagger = \case
    InjL f -> InjL (dagger f)
    InjR f -> InjR (dagger f)
