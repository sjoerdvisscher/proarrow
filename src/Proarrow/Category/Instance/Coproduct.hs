module Proarrow.Category.Instance.Coproduct where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)

data COPRODUCT j k = L j | R k

type (:++:) :: CAT j -> CAT k -> CAT (COPRODUCT j k)
data (c :++: d) a b where
  InjL :: c a b -> (c :++: d) (L a) (L b)
  InjR :: d a b -> (c :++: d) (R a) (R b)

class IsEither (a :: COPRODUCT j k) where
  eitherId :: ((~>) :++: (~>)) a a
instance (Ob a, Category ((~>) :: CAT k)) => IsEither (L (a :: k)) where
  eitherId = InjL id
instance (Ob a, Category ((~>) :: CAT k)) => IsEither (R (a :: k)) where
  eitherId = InjR id

type instance (~>) = (~>) :++: (~>)

-- | The coproduct category of the categories `c` and `d`.
instance (Category c, Category d) => Category (c :++: d) where
  type Ob a = IsEither a
  id = eitherId
  InjL f . InjL g = InjL (f . g)
  InjR f . InjR g = InjR (f . g)

instance (Category c, Category d) => Profunctor (c :++: d) where
  dimap = dimapDefault
  r \\ InjL f = r \\ f
  r \\ InjR f = r \\ f