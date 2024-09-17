module Proarrow.Category.Instance.Coproduct where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, Category, CategoryOf (..), Profunctor (..), Promonad (..))
import Proarrow.Preorder.ThinCategory (Thin (..))

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
instance (Category c, Category d) => Promonad (c :++: d) where
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

class HasArrowCoprod (a :: COPRODUCT j k) b where arrCoprod :: a ~> b
instance (Thin j, HasArrow (a :: j) b, Ob a, Ob b) => HasArrowCoprod (L a) (L b) where arrCoprod = InjL (arr @j)
instance (Thin k, HasArrow (a :: k) b, Ob a, Ob b) => HasArrowCoprod (R a) (R b) where arrCoprod = InjR (arr @k)

instance (Thin j, Thin k) => Thin (COPRODUCT j k) where
  type HasArrow a b = HasArrowCoprod a b
  arr = arrCoprod
  withArr (InjL f) r = withArr f r \\ f
  withArr (InjR f) r = withArr f r \\ f