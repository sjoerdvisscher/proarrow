module Proarrow.Category.Enriched.Dagger where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor, type (+->))

class (Dagger k, Profunctor p) => DaggerProfunctor (p :: k +-> k) where
  dagger :: p a b -> p b a

class (DaggerProfunctor ((~>) :: CAT k)) => Dagger k
instance (DaggerProfunctor ((~>) :: CAT k)) => Dagger k
