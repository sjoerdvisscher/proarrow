module Proarrow.Category.Instance.Sub where

import Proarrow.Core (CAT, OB, UN, Is, CategoryOf (..), Promonad (..), Profunctor (..), dimapDefault)
import Proarrow.Category.Monoidal (Monoidal (..), SymMonoidal (..))


type data SUBCAT (ob :: OB k) = SUB k
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

class (CategoryOf k, ob (a ** b)) => IsObMult (ob :: OB k) a b
instance (CategoryOf k, ob (a ** b)) => IsObMult (ob :: OB k) a b

instance (Monoidal k, ob Unit, forall a b. (ob a, ob b) => IsObMult ob a b) => Monoidal (SUBCAT (ob :: OB k)) where
  type Unit = SUB Unit
  type a ** b = SUB (UN SUB a ** UN SUB b)
  Sub f `par` Sub g = Sub (f `par` g)
  leftUnitor (Sub a) = Sub (leftUnitor a)
  leftUnitorInv (Sub a) = Sub (leftUnitorInv a)
  rightUnitor (Sub a) = Sub (rightUnitor a)
  rightUnitorInv (Sub a) = Sub (rightUnitorInv a)
  associator (Sub a) (Sub b) (Sub c) = Sub (associator a b c)
  associatorInv (Sub a) (Sub b) (Sub c) = Sub (associatorInv a b c)

instance (SymMonoidal k, ob Unit, forall a b. (ob a, ob b) => IsObMult ob a b) => SymMonoidal (SUBCAT (ob :: OB k)) where
  swap' (Sub a) (Sub b) = Sub (swap' a b)