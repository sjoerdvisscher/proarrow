{-# LANGUAGE UndecidableInstances #-}
module Proarrow.Profunctor.Forget where

import Prelude (Monoid(..), map, foldMap)
import Data.Kind (Type)

import Proarrow.Category.Instance.Subcategory (SUB(..), Sub (..))
import Proarrow.Core (OB, PRO, Profunctor(..), Category(..), type (~>), CategoryOf)
import Proarrow.Adjunction (Adjunction(..))
import Proarrow.Profunctor.Composition ((:.:)(..))
import Proarrow.Profunctor.Representable (Representable(..))


type Forget :: forall (ob :: OB k) -> PRO k (SUB ob)
data Forget ob a b where
  Forget :: ob b => a ~> b -> Forget ob a ('SUB b)

instance CategoryOf k => Profunctor (Forget (ob :: OB k)) where
  dimap l (Sub r) (Forget f) = Forget (r . f . l)
  r \\ Forget f = r \\ f

instance CategoryOf k => Representable (Forget (ob :: OB k)) where
  type Forget ob % ('SUB a) = a
  index (Forget f) = f
  tabulate = Forget
  repMap (Sub f) = f

type List :: PRO (SUB Monoid) Type
data List a b where
  List :: Monoid a => (a -> [b]) -> List ('SUB a) b
instance Profunctor List where
  dimap (Sub l) r (List f) = List (map r . f . l)
  r \\ List{} = r

instance Representable List where
  type List % a = 'SUB [a]
  index (List f) = Sub f
  tabulate (Sub f) = List f
  repMap f = Sub (map f)

instance Adjunction List (Forget Monoid) where
  unit = List id :.: Forget (:[])
  counit (Forget f :.: List g) = Sub (foldMap f . g)