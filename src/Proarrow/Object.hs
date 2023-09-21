module Proarrow.Object where

import Proarrow.Category (type (~>), CategoryOf, Category (..))
import Proarrow.Profunctor (Profunctor (..))

type Obj a = a ~> a
obj :: forall {k} (a :: k). (CategoryOf k, Ob a) => Obj a
obj = id @k @_ @a
src :: forall {k} a b p. Profunctor p => p (a :: k) b -> Obj a
src p = obj @a \\ p
tgt :: forall {k} a b p. Profunctor p => p (a :: k) b -> Obj b
tgt p = obj @b \\ p

class Ob a => Ob' a
instance Ob a => Ob' a
type VacuusOb k = forall a. Ob' (a :: k)
