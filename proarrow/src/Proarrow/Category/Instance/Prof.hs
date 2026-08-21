{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Prof where

import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, (:~>), type (+->))

type Prof :: CAT (j +-> k)
data Prof p q where
  Prof
    :: (Profunctor p, Profunctor q)
    => {unProf :: p :~> q}
    -> Prof p q

-- | The category of profunctors and natural transformations between them.
instance CategoryOf (j +-> k) where
  type (~>) = Prof
  type Ob p = Profunctor p

instance Promonad Prof where
  id = Prof id
  Prof f . Prof g = Prof (f . g)

instance Profunctor Prof where
  dimap = dimapDefault
  r \\ Prof{} = r
