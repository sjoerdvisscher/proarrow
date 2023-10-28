{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Proarrow.Category.Instance.List where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf(..), Promonad(..), Profunctor(..), dimapDefault)
import Proarrow.Object (obj)


type List :: CAT [k]
-- | The free monoid in CAT
data List as bs where
  Nil :: List '[] '[]
  Cons :: a ~> b -> List as bs -> List (a ': as) (b ': bs)

class IsList as where listId :: List as as
instance IsList '[] where listId = Nil
instance (CategoryOf k, Ob (a :: k), IsList as) => IsList (a ': as) where listId = Cons id id

instance CategoryOf k => CategoryOf [k] where
  type (~>) = List
  type Ob as = IsList as

instance CategoryOf k => Promonad (List :: CAT [k]) where
  id = listId
  Nil . Nil = Nil
  Cons f fs . Cons g gs = Cons (f . g) (fs . gs)

instance CategoryOf k => Profunctor (List :: CAT [k]) where
  dimap = dimapDefault
  r \\ Nil = r
  r \\ Cons f fs = r \\ f \\ fs


type family All (pred :: k -> Constraint) (as :: [k]) :: Constraint where
  All pred '[] = () :: Constraint
  All pred (a ': as) = (pred a, All pred as)

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

append :: List a1 b1 -> List a2 b2 -> List (a1 ++ a2) (b1 ++ b2)
append Nil bs = bs
append (Cons a as) bs = Cons a (append as bs)

obAppend :: forall {k} (as :: [k]) bs r. (CategoryOf k, Ob as, Ob bs) => (Ob (as ++ bs) => r) -> r
obAppend r = r \\ append (obj @as) (obj @bs)
