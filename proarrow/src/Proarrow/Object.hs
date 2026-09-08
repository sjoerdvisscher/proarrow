-- | Working with objects through their identity arrows: 'Obj' @a@ is @a '~>' a@ used as a witness that
-- @a@ is an object, with 'obj', 'src' and 'tgt' to produce them and the 'Obj'\/'Objs' pattern synonyms
-- to recover 'Ob' constraints from arrows and profunctor values.
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

import Proarrow.Core (CategoryOf (..), Obj, Profunctor, obj, src, tgt, (\\))

-- | 'Ob' as a proper class, for the positions where the type family 'Ob' itself cannot appear,
-- such as the head of a quantified constraint.
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

-- | Matching a profunctor value @p a b@ against 'Objs' brings @('Ob' a, 'Ob' b)@ into scope --
-- the pattern form of '(\\)', handy in function equations.
pattern Objs :: (Profunctor p) => (Ob a, Ob b) => p a b
pattern Objs <- (objDicts -> (ObjDict, ObjDict))

{-# COMPLETE Objs #-}
