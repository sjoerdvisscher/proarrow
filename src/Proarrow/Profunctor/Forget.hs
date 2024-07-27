module Proarrow.Profunctor.Forget where

import Data.Kind (Type)
import Prelude (Monoid (..), foldMap, map)

import Proarrow.Adjunction (Adjunction (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Core (CategoryOf (..), OB, PRO, Profunctor (..), Promonad (..))
import Proarrow.Profunctor.Composition ((:.:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

type Forget :: forall (ob :: OB k) -> PRO k (SUBCAT ob)
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

type List :: PRO (SUBCAT Monoid) Type
data List a b where
  List :: (Monoid a) => (a -> [b]) -> List (SUB a) b
instance Profunctor List where
  dimap = dimapRep
  r \\ List{} = r

instance Representable List where
  type List % a = SUB [a]
  index (List f) = Sub f
  tabulate (Sub f) = List f
  repMap f = Sub (map f)

instance Adjunction List (Forget Monoid) where
  unit = Forget (: []) :.: List id
  counit (List g :.: Forget f) = Sub (foldMap f . g)
