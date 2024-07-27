module Proarrow.Category.Instance.Coproduct where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), IsCategoryOf, Profunctor (..), Promonad (..))

data COPRODUCT j k = L j | R k

type (:++:) :: CAT j -> CAT k -> CAT (COPRODUCT j k)
data (c :++: d) a b where
  InjL :: c a b -> (c :++: d) (L a) (L b)
  InjR :: d a b -> (c :++: d) (R a) (R b)

type IsCoproduct :: forall {j} {k}. COPRODUCT j k -> Constraint
class IsCoproduct (a :: COPRODUCT j k) where
  coproductId :: ((~>) :++: (~>)) a a
instance (Ob a, Promonad ((~>) :: CAT k)) => IsCoproduct (L (a :: k)) where
  coproductId = InjL id
instance (Ob a, Promonad ((~>) :: CAT k)) => IsCoproduct (R (a :: k)) where
  coproductId = InjR id

instance (CategoryOf j, CategoryOf k) => CategoryOf (COPRODUCT j k) where
  type (~>) = (~>) :++: (~>)
  type Ob a = IsCoproduct a

-- | The coproduct category of the categories `c` and `d`.
instance (IsCategoryOf j c, IsCategoryOf k d) => Promonad ((c :++: d) :: CAT (COPRODUCT j k)) where
  id = coproductId
  InjL f . InjL g = InjL (f . g)
  InjR f . InjR g = InjR (f . g)

instance (Profunctor c, Profunctor d) => Profunctor (c :++: d) where
  dimap (InjL l) (InjL r) (InjL f) = InjL (dimap l r f)
  dimap (InjR l) (InjR r) (InjR f) = InjR (dimap l r f)
  dimap (InjL _) (InjR _) f = case f of {}
  dimap (InjR _) (InjL _) f = case f of {}
  r \\ InjL f = r \\ f
  r \\ InjR f = r \\ f
