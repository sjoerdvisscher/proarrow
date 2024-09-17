module Proarrow.Profunctor.Forget where

import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), OB, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Representable (Representable (..))

type Forget :: forall (ob :: OB k) -> SUBCAT ob +-> k
data Forget ob a b where
  Forget :: (ob b) => a ~> b -> Forget ob a (SUB b)

instance (CategoryOf k) => Profunctor (Forget (ob :: OB k)) where
  dimap l (Sub r) (Forget f) = Forget (r . f . l)
  r \\ Forget f = r \\ f

instance (CategoryOf k) => Representable (Forget (ob :: OB k)) where
  type Forget ob % (SUB a) = a
  index (Forget f) = f
  tabulate = Forget
  repMap (Sub f) = f
