module Proarrow.Category.Dagger where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor)

class (Profunctor p) => DaggerProfunctor p where
  dagger :: p a b -> p b a

class (DaggerProfunctor ((~>) :: CAT k)) => Dagger k
instance (DaggerProfunctor ((~>) :: CAT k)) => Dagger k
