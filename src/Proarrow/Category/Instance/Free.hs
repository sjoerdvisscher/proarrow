module Proarrow.Category.Instance.Free where

import Data.Kind (Type)

import Proarrow.Core (CAT, Category(..), Profunctor(..), (:~>), dimapDefault)
import Proarrow.Object (VacuusOb)
import Proarrow.Promonad (Promonad(..))
import Proarrow.Profunctor.Composition ((:.:)(..))

infixr 4 :|

type Free :: (k -> k -> Type) -> CAT k
data Free g a b where
  FreeId :: Free g a a
  (:|) :: g a b -> Free g b c -> Free g a c

instance (Category (Free g), VacuusOb k) => Profunctor (Free (g :: k -> k -> Type)) where
  dimap = dimapDefault

class Rewrite g where
  rewriteAfterCons :: Free g :~> Free g

instance (Rewrite g, Category (Free g), VacuusOb k) => Promonad (Free (g :: k -> k -> Type)) where
  unit f = f
  mult (FreeId :.: a) = a
  mult (a :.: FreeId) = a
  mult (a :.: (g :| b)) = rewriteAfterCons (g :| mult (a :.: b))
