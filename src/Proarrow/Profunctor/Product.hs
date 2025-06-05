module Proarrow.Profunctor.Product where

import Proarrow.Category.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Profunctor (..), (:~>), type (+->))

type (:*:) :: (j +-> k) -> (j +-> k) -> (j +-> k)
data (p :*: q) a b where
  (:*:) :: {fstP :: p a b, sndP :: q a b} -> (p :*: q) a b

prod :: (r :~> p) -> (r :~> q) -> r :~> p :*: q
prod l r p = l p :*: r p

instance (Profunctor p, Profunctor q) => Profunctor (p :*: q) where
  dimap l r (p :*: q) = dimap l r p :*: dimap l r q
  r \\ (p :*: _) = r \\ p

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :*: q) where
  par0 = par0 :*: par0
  par (p1 :*: p2) (q1 :*: q2) = par p1 q1 :*: par p2 q2

instance (DaggerProfunctor p, DaggerProfunctor q) => DaggerProfunctor (p :*: q) where
  dagger (p :*: q) = dagger p :*: dagger q