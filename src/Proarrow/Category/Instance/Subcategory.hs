module Proarrow.Category.Instance.Subcategory where

import Proarrow.Core (CAT, OB, UN, Is, CategoryOf(..), Promonad(..), Profunctor(..), dimapDefault)


newtype SUBCAT (ob :: OB k) = SUB k
type instance UN SUB (SUB k) = k

type Sub :: CAT (SUBCAT ob)
data Sub a b where
  Sub :: (ob a, ob b) => a ~> b -> Sub (SUB a :: SUBCAT ob) (SUB b)

instance Profunctor ((~>) :: CAT k) => Profunctor (Sub :: CAT (SUBCAT (ob :: OB k))) where
  dimap = dimapDefault
  r \\ Sub p = r \\ p

instance Promonad ((~>) :: CAT k) => Promonad (Sub :: CAT (SUBCAT (ob :: OB k))) where
  id = Sub id
  Sub f . Sub g = Sub (f . g)

-- | The subcategory with objects with instances of the given constraint `ob`.
instance CategoryOf k => CategoryOf (SUBCAT (ob :: OB k)) where
  type (~>) = Sub
  type Ob (a :: SUBCAT ob) = (Is SUB a, Ob (UN SUB a), ob (UN SUB a))
