module Proarrow.Profunctor.Coproduct where

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Core (Profunctor (..), type (+->))
import Proarrow.Category.Monoidal.Action (Strong (..))

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

instance (Strong m p, Strong m q) => Strong m (p :+: q) where
  act f (InjL p) = InjL (act f p)
  act f (InjR q) = InjR (act f q)