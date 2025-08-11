module Proarrow.Profunctor.Product where

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (Profunctor (..), (:~>), type (+->))
import Proarrow.Category.Monoidal.Action (Strong (..))
import Proarrow.Category.Enriched.ThinCategory (ThinProfunctor (..))

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

instance (ThinProfunctor p, ThinProfunctor q) => ThinProfunctor (p :*: q) where
  type HasArrow (p :*: q) a b = (HasArrow p a b, HasArrow q a b)
  arr = arr :*: arr
  withArr (p :*: q) r = withArr p (withArr q r)

instance (Strong m p, Strong m q) => Strong m (p :*: q) where
  act f (p :*: q) = act f p :*: act f q