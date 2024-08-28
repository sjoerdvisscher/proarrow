module Proarrow.Profunctor.Product where

import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (PRO, Profunctor (..), (:~>))

type (:*:) :: PRO j k -> PRO j k -> PRO j k
data (p :*: q) a b where
  (:*:) :: {fstP :: p a b, sndP :: q a b} -> (p :*: q) a b

instance (Profunctor p, Profunctor q) => Profunctor (p :*: q) where
  dimap l r (p :*: q) = dimap l r p :*: dimap l r q
  r \\ (p :*: _) = r \\ p

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :*: q) where
  par0 = par0 :*: par0
  par (p1 :*: p2) (q1 :*: q2) = par p1 q1 :*: par p2 q2

prod :: (r :~> p) -> (r :~> q) -> r :~> p :*: q
prod l r p = l p :*: r p
