{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Category.Instance.Coproduct where

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)
import Prelude (Either(..))

type (:++:) :: CAT k1 -> CAT k2 -> CAT (Either k1 k2)
data (c :++: d) a b where
  L :: c a b -> (c :++: d) ('Left a) ('Left b)
  R :: d a b -> (c :++: d) ('Right a) ('Right b)

class IsEither (a :: Either k1 k2) where
  eitherId :: ((~>) :++: (~>)) a a
instance (Ob a, Category ((~>) :: CAT k)) => IsEither ('Left (a :: k)) where
  eitherId = L id
instance (Ob a, Category ((~>) :: CAT k)) => IsEither ('Right (a :: k)) where
  eitherId = R id

type instance (~>) = (~>) :++: (~>)

instance (Category c, Category d) => Category (c :++: d) where
  type Ob a = IsEither a
  id = eitherId
  L f . L g = L (f . g)
  R f . R g = R (f . g)

instance (Category c, Category d) => Profunctor (c :++: d) where
  dimap = dimapDefault
  r \\ L f = r \\ f
  r \\ R f = r \\ f