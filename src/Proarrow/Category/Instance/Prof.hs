module Proarrow.Category.Instance.Prof where

import Proarrow.Core (CAT, PRO, Category(..), Profunctor(..), type (~>), dimapDefault, (:~>))

type Prof :: CAT (PRO j k)
data Prof p q where
  Prof :: (Profunctor p, Profunctor q)
      => { getProf :: p :~> q }
      -> Prof p q

type instance (~>) = Prof

-- | The category of profunctors and natural transformations between them.
instance Category Prof where
  type Ob p = Profunctor p
  id = Prof id
  Prof f . Prof g = Prof (f . g)

instance Profunctor Prof where
  dimap = dimapDefault
  r \\ Prof{} = r

