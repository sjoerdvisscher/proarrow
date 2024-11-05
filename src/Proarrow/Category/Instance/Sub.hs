module Proarrow.Category.Instance.Sub where

import Data.Kind (Type, Constraint)

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, OB, Profunctor (..), Promonad (..), UN)
import Proarrow.Profunctor.Representable (Representable (..))

type SUBCAT :: forall {k}. OB k -> Type
type data SUBCAT (ob :: OB k) = SUB k
type instance UN SUB (SUB k) = k

type Sub :: CAT k -> CAT (SUBCAT (ob :: OB k))
data Sub p a b where
  Sub :: (ob a, ob b) => { unSub :: p a b } -> Sub p (SUB a :: SUBCAT ob) (SUB b)

instance (Profunctor p) => Profunctor (Sub p) where
  dimap (Sub l) (Sub r) (Sub p) = Sub (dimap l r p)
  r \\ Sub p = r \\ p

instance (Promonad p) => Promonad (Sub p) where
  id = Sub id
  Sub f . Sub g = Sub (f . g)

-- | The subcategory with objects with instances of the given constraint `ob`.
instance (CategoryOf k) => CategoryOf (SUBCAT (ob :: OB k)) where
  type (~>) = Sub (~>)
  type Ob (a :: SUBCAT ob) = (Is SUB a, Ob (UN SUB a), ob (UN SUB a))

type On :: (k -> Constraint) -> forall (ob :: OB k) -> SUBCAT ob -> Constraint
class (c (UN SUB a)) => (c `On` ob) a
instance (c (UN SUB a)) => (c `On` ob) a

class (CategoryOf k, ob (a ** b)) => IsObMult (ob :: OB k) a b
instance (CategoryOf k, ob (a ** b)) => IsObMult (ob :: OB k) a b

instance (MonoidalProfunctor p, ob Unit, forall a b. (ob a, ob b) => IsObMult ob a b) => MonoidalProfunctor (Sub p :: CAT (SUBCAT (ob :: OB k))) where
  par0 = Sub par0
  Sub f `par` Sub g = Sub (f `par` g)

instance (Monoidal k, ob Unit, forall a b. (ob a, ob b) => IsObMult ob a b) => Monoidal (SUBCAT (ob :: OB k)) where
  type Unit = SUB Unit
  type a ** b = SUB (UN SUB a ** UN SUB b)
  leftUnitor (Sub a) = Sub (leftUnitor a)
  leftUnitorInv (Sub a) = Sub (leftUnitorInv a)
  rightUnitor (Sub a) = Sub (rightUnitor a)
  rightUnitorInv (Sub a) = Sub (rightUnitorInv a)
  associator (Sub a) (Sub b) (Sub c) = Sub (associator a b c)
  associatorInv (Sub a) (Sub b) (Sub c) = Sub (associatorInv a b c)

instance (SymMonoidal k, ob Unit, forall a b. (ob a, ob b) => IsObMult ob a b) => SymMonoidal (SUBCAT (ob :: OB k)) where
  swap' (Sub a) (Sub b) = Sub (swap' a b)

instance (Representable p, forall a. ob a => ob (p % a)) => Representable (Sub p :: CAT (SUBCAT (ob :: OB k))) where
  type Sub p % a = SUB (p % UN SUB a)
  index (Sub p) = Sub (index p)
  tabulate (Sub f) = Sub (tabulate f)
  repMap (Sub f) = Sub (repMap @p f)
