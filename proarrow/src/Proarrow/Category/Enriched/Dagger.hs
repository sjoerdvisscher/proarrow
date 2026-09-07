-- | Dagger categories: a 'DaggerProfunctor' has an identity-on-objects involution
-- @'dagger' :: p a b -> p b a@, and a category is 'Dagger' when its hom-profunctor is one.
module Proarrow.Category.Enriched.Dagger where

import Proarrow.Core (Hom, Profunctor, type (+->))

class (Dagger k, Profunctor p) => DaggerProfunctor (p :: k +-> k) where
  dagger :: p a b -> p b a

type Dagger k = DaggerProfunctor (Hom k)
