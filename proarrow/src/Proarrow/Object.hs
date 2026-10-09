{-# LANGUAGE AllowAmbiguousTypes #-}

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
  , VacuousOb
  , objDicts
  , ObjDict (..)

    -- * Lists of objects
  , type (++)
  , ListOf (..)
  , KnownListOf (..)
  , withKnownListOf
  , mapListOf
  , lengthListOf
  , appendListOf
  , eqListOf

    -- * One object of many
  , SomeOf (..)
  , someOfList
  , withListOf
  , someRepOf
  ) where

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (..))
import Type.Reflection (SomeTypeRep (..), Typeable, typeRep)
import Prelude (Int, (+))
import Prelude qualified as P

import Proarrow.Core (CategoryOf (..), OB, Ob', Obj, Profunctor, VacuousOb, obj, src, tgt, (\\), type (:&&:))

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

-- | Matching a profunctor value @p a b@ against 'Objs' brings @('Ob' a, 'Ob' b)@ into scope. This
-- is the pattern form of '(\\)', handy in function equations.
pattern Objs :: (Profunctor p) => (Ob a, Ob b) => p a b
pattern Objs <- (objDicts -> (ObjDict, ObjDict))

{-# COMPLETE Objs #-}

-- | A type-level list with the evidence @c@ for each element, as a value.
type ListOf :: forall {k}. OB k -> [k] -> Type
data ListOf c xs where
  Nil :: ListOf c '[]
  Cons :: forall {k} {c :: OB k} (x :: k) xs. (c x) => ListOf c xs -> ListOf c (x ': xs)

-- | A type-level list whose elements have the evidence @c@, as its 'ListOf'.
type KnownListOf :: forall {k}. OB k -> [k] -> Constraint
class KnownListOf c xs where
  listOf :: ListOf c xs

instance KnownListOf c '[] where
  listOf = Nil
instance (c x, KnownListOf c xs) => KnownListOf c (x ': xs) where
  listOf = Cons @x listOf

-- | The class from the list.
withKnownListOf :: ListOf c xs -> ((KnownListOf c xs) => r) -> r
withKnownListOf Nil r = r
withKnownListOf (Cons rest) r = withKnownListOf rest r

-- | A value for each element, in order.
mapListOf :: forall {k} (c :: OB k) xs r. (forall (x :: k). (c x) => r) -> ListOf c xs -> [r]
mapListOf _ Nil = []
mapListOf f (Cons @x rest) = f @x : mapListOf @c (\ @y -> f @y) rest

-- | The number of elements.
lengthListOf :: ListOf c xs -> Int
lengthListOf Nil = 0
lengthListOf (Cons rest) = 1 + lengthListOf rest

-- | List concatenation.
type (++) :: [k] -> [k] -> [k]
type family as ++ bs where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

-- | Whether two lists have the same elements, given how to decide that for one element.
eqListOf
  :: forall {k} (c :: OB k) as bs
   . (forall (x :: k) (y :: k). (c x, c y) => P.Maybe (x :~: y))
  -> ListOf c as
  -> ListOf c bs
  -> P.Maybe (as :~: bs)
eqListOf _ Nil Nil = P.Just Refl
eqListOf eq (Cons @x xs) (Cons @y ys) = case (eq @x @y, eqListOf @c eq xs ys) of
  (P.Just Refl, P.Just Refl) -> P.Just Refl
  _ -> P.Nothing
eqListOf _ _ _ = P.Nothing

-- | The elements of both lists.
appendListOf :: ListOf c as -> ListOf c bs -> ListOf c (as ++ bs)
appendListOf Nil ys = ys
appendListOf (Cons @x xs) ys = Cons @x (appendListOf xs ys)

-- | Some type with the evidence @c@, which one known only at runtime.
type SomeOf :: forall {k}. OB k -> Type
data SomeOf c where
  Some :: forall {k} {c :: OB k} (x :: k). (c x) => SomeOf c

-- | The elements of the list, each on its own.
someOfList :: forall {k} (c :: OB k) xs. ListOf c xs -> [SomeOf c]
someOfList = mapListOf (\ @x -> Some @x)

-- | A list of types known at runtime as a type-level list.
withListOf :: forall {k} (c :: OB k) r. [SomeOf c] -> (forall (xs :: [k]). ListOf c xs -> r) -> r
withListOf [] k = k Nil
withListOf (Some @x : rest) k = withListOf rest (\l -> k (Cons @x l))

-- | The type representation of the type, which is what 'SomeOf' values are compared and shown by.
someRepOf :: SomeOf (Typeable :&&: c) -> SomeTypeRep
someRepOf (Some @x) = SomeTypeRep (typeRep @x)

instance P.Eq (SomeOf (Typeable :&&: c)) where
  x == y = someRepOf x P.== someRepOf y
instance P.Ord (SomeOf (Typeable :&&: c)) where
  compare x y = P.compare (someRepOf x) (someRepOf y)
instance P.Show (SomeOf (Typeable :&&: c)) where
  show = P.show P.. someRepOf
