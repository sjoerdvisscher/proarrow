module Proarrow.Category.Instance.Coproduct where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, Category(..), Profunctor(..), type (~>), dimapDefault)

data COPRODUCT j k = L j | R k

type (:++:) :: CAT j -> CAT k -> CAT (COPRODUCT j k)
data (c :++: d) a b where
  InjL :: c a b -> (c :++: d) (L a) (L b)
  InjR :: d a b -> (c :++: d) (R a) (R b)

type IsCoproduct :: forall {j} {k}. COPRODUCT j k -> Constraint
class IsCoproduct (a :: COPRODUCT j k) where
  coproductId :: ((~>) :++: (~>)) a a
instance (Ob a, Category ((~>) :: CAT k)) => IsCoproduct (L (a :: k)) where
  coproductId = InjL id
instance (Ob a, Category ((~>) :: CAT k)) => IsCoproduct (R (a :: k)) where
  coproductId = InjR id

type instance (~>) = (~>) :++: (~>)

-- | The coproduct category of the categories `c` and `d`.
instance (Category c, Category d) => Category (c :++: d) where
  type Ob a = IsCoproduct a
  id = coproductId
  InjL f . InjL g = InjL (f . g)
  InjR f . InjR g = InjR (f . g)

instance (Category c, Category d) => Profunctor (c :++: d) where
  dimap = dimapDefault
  r \\ InjL f = r \\ f
  r \\ InjR f = r \\ f