module Proarrow.Object
  ( Obj
  , pattern Obj
  , pattern Objs
  , obj
  , src
  , tgt
  , Ob'
  , VacuusOb
  , objDicts
  , ObjDict (..)
  ) where

import Data.Kind (Type)

import Proarrow.Core (CategoryOf (..), Obj, obj, src, tgt, (\\), Profunctor)

class (Ob a, CategoryOf k) => Ob' (a :: k)
instance (Ob a, CategoryOf k) => Ob' (a :: k)
type VacuusOb k = forall a. Ob' (a :: k)

type ObjDict :: forall {k}. k -> Type
data ObjDict a where
  ObjDict :: (Ob a) => ObjDict a

objDicts :: (Profunctor p) => p a a' -> (ObjDict a, ObjDict a')
objDicts a = (ObjDict \\ a, ObjDict \\ a)

pattern Obj :: (CategoryOf k) => (Ob (a :: k)) => Obj a
pattern Obj <- (objDicts -> (ObjDict, ObjDict))
  where
    Obj = obj

{-# COMPLETE Obj #-}

pattern Objs :: (Profunctor p) => (Ob a, Ob b) => p a b
pattern Objs <- (objDicts -> (ObjDict, ObjDict))

{-# COMPLETE Objs #-}