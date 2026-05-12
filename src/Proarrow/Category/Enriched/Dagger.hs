module Proarrow.Category.Enriched.Dagger where

import Proarrow.Core (Hom, Profunctor, type (+->))

class (Dagger k, Profunctor p) => DaggerProfunctor (p :: k +-> k) where
  dagger :: p a b -> p b a

type Dagger k = DaggerProfunctor (Hom k)
