module Proarrow.Profunctor.Instance.Coproduct where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (Profunctor (..), type (+->))
import Proarrow.Functor (Functor (..))

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
