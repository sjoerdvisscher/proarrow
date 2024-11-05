module Proarrow.Object
  ( Obj
  , pattern Obj
  , pattern Objs
  , obj
  , src
  , tgt
  , Ob'
  , VacuusOb
  ) where

import Data.Kind (Type)

import Proarrow.Core (CategoryOf (..), Obj, obj, src, tgt, (\\))

class (Ob a) => Ob' a
instance (Ob a) => Ob' a
type VacuusOb k = forall a. Ob' (a :: k)

type ObjDict :: forall {k}. k -> Type
data ObjDict a where
  ObjDict :: (Ob a) => ObjDict a

objDict :: (CategoryOf k) => a ~> a' -> (ObjDict (a :: k), ObjDict a')
objDict a = (ObjDict \\ a, ObjDict \\ a)

pattern Obj :: (CategoryOf k) => (Ob (a :: k)) => Obj a
pattern Obj <- (objDict -> (ObjDict, ObjDict))
  where
    Obj = obj

pattern Objs :: (CategoryOf k) => (Ob (a :: k), Ob (b :: k)) => a ~> b
pattern Objs <- (objDict -> (ObjDict, ObjDict))