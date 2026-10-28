-- | Coproduct constructions for profunctors. A @(p ':+:' q) a b@ is either a
-- @p a b@ or a @q a b@; 'Sum' instead takes the coproduct of represented objects.
module Proarrow.Profunctor.Instance.Coproduct where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (Profunctor (..), type (+->))
import Proarrow.Functor (Functor (..))
import Proarrow.Profunctor.Instance.Product ((:*:))
import Proarrow.Profunctor.Representable (CorepStar, RepCostar)

type (:+:) :: (j +-> k) -> (j +-> k) -> (j +-> k)
data (p :+: q) a b where
  InjL :: p a b -> (p :+: q) a b
  InjR :: q a b -> (p :+: q) a b

instance (Profunctor p, Profunctor q) => Profunctor (p :+: q) where
  dimap l r (InjL p) = InjL (dimap l r p)
  dimap l r (InjR q) = InjR (dimap l r q)
  r \\ InjL p = r \\ p
  r \\ InjR q = r \\ q

coproduct :: (p x y -> r) -> (q x y -> r) -> (p :+: q) x y -> r
coproduct l _ (InjL p) = l p
coproduct _ r (InjR q) = r q

instance (DaggerProfunctor p, DaggerProfunctor q) => DaggerProfunctor (p :+: q) where
  dagger (InjL p) = InjL (dagger p)
  dagger (InjR q) = InjR (dagger q)

instance (Profunctor p) => Functor ((:+:) p) where
  map (Prof n) = Prof \case
    InjL p -> InjL p
    InjR q -> InjR (n q)

-- | The pointwise coproduct of represented functors, with object action
-- @Sum f g % b = (f % b) || (g % b)@. It is representable when @f@ and @g@
-- are representable and their target category has binary coproducts; the
-- required instance is supplied by "Proarrow.Colimit.BinaryCoproduct".
--
-- Whereas @(f :+: g) a b@ chooses between arrows into the two summands,
-- @Sum f g a b@ represents an arrow into their coproduct. In @Type@ these
-- are @Either (a -> f % b) (a -> g % b)@ and @a -> Either (f % b) (g % b)@.
type Sum :: (j +-> k) -> (j +-> k) -> (j +-> k)
type Sum f g = CorepStar (RepCostar f :*: RepCostar g)
