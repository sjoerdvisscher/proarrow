module Proarrow.Category.Instance.Subcategory where

import Proarrow.Core (CAT, OB, UN, Is, Category(..), Profunctor(..), type (~>), dimapDefault)


newtype SUBCAT (ob :: OB k) = SUB k
type instance UN SUB (SUB k) = k

type Sub :: CAT (SUBCAT ob)
data Sub a b where
  Sub :: (ob a, ob b) => a ~> b -> Sub (SUB a :: SUBCAT ob) (SUB b)

type instance (~>) = Sub

instance Profunctor ((~>) :: CAT k) => Profunctor (Sub :: CAT (SUBCAT (ob :: OB k))) where
  dimap = dimapDefault
  r \\ Sub p = r \\ p

-- | The subcategory with objects with instances of the given constraint `ob`.
instance Category ((~>) :: CAT k) => Category (Sub :: CAT (SUBCAT (ob :: OB k))) where
  type Ob (a :: SUBCAT ob) = (Is SUB a, Ob (UN SUB a), ob (UN SUB a))
  id = Sub id
  Sub f . Sub g = Sub (f . g)