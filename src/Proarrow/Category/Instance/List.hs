{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.List where

import Proarrow.Category.Monoidal (Monoidal (..), type (++))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault)

type data LIST k = L [k]
type instance UN L (L as) = as

type List :: CAT (LIST k)

-- | The free monoid in CAT
data List as bs where
  Nil :: List (L '[]) (L '[])
  Cons :: (IsList as, IsList bs) => a ~> b -> List (L as) (L bs) -> List (L (a ': as)) (L (b ': bs))

mkCons :: (CategoryOf k) => (a :: k) ~> b -> L as ~> L bs -> L (a ': as) ~> L (b ': bs)
mkCons f fs = Cons f fs \\ fs

class IsList as where listId :: List (L as) (L as)
instance IsList '[] where listId = Nil
instance (CategoryOf k, Ob (a :: k), IsList as) => IsList (a ': as) where listId = Cons id id

instance (CategoryOf k) => CategoryOf (LIST k) where
  type (~>) = List
  type Ob as = (Is L as, IsList (UN L as))

instance (CategoryOf k) => Promonad (List :: CAT (LIST k)) where
  id = listId
  Nil . Nil = Nil
  Cons f fs . Cons g gs = Cons (f . g) (fs . gs)

instance (CategoryOf k) => Profunctor (List :: CAT (LIST k)) where
  dimap = dimapDefault
  r \\ Nil = r
  r \\ Cons f fs = r \\ f \\ fs

instance (CategoryOf k) => Monoidal (LIST k) where
  type Unit = L '[]
  type p ** q = L (UN L p ++ UN L q)
  Nil `par` Nil = Nil
  Nil `par` gs@Cons{} = gs
  Cons f fs `par` Nil = mkCons f (fs `par` Nil)
  Cons f fs `par` Cons g gs = mkCons f (fs `par` Cons g gs)
  leftUnitor f = listId \\ f
  leftUnitorInv f = listId \\ f
  rightUnitor Nil = listId
  rightUnitor (Cons f fs) = mkCons f (rightUnitor fs)
  rightUnitorInv Nil = listId
  rightUnitorInv (Cons f fs) = mkCons f (rightUnitorInv fs)
  associator Nil bs cs = listId \\ bs `par` cs
  associator (Cons f fs) bs cs = mkCons f (associator fs bs cs)
  associatorInv Nil bs cs = listId \\ bs `par` cs
  associatorInv (Cons f fs) bs cs = mkCons f (associatorInv fs bs cs)
