{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.List where

import Prelude (type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Strictified (type (++))
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

class ((as ++ bs) ++ cs ~ as ++ (bs ++ cs)) => Assoc as bs cs
instance (as ++ (bs ++ cs) ~ (as ++ bs) ++ cs) => Assoc as bs cs
class (as ~ as ++ '[], forall bs cs. Assoc as bs cs) => IsList as where
  listId :: List (L as) (L as)
  withIsList2 :: IsList bs => (IsList (as ++ bs) => r) -> r
instance IsList '[] where
  listId = Nil
  withIsList2 r = r
instance (CategoryOf k, Ob (a :: k), IsList as) => IsList (a ': as) where
  listId = Cons id listId
  withIsList2 @bs r = withIsList2 @as @bs r

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

instance (CategoryOf k) => MonoidalProfunctor (List :: CAT (LIST k)) where
  par0 = Nil
  Nil `par` Nil = Nil
  Nil `par` gs@Cons{} = gs
  Cons f fs `par` Nil = mkCons f (fs `par` Nil)
  Cons f fs `par` Cons g gs = mkCons f (fs `par` Cons g gs)

instance (CategoryOf k) => Monoidal (LIST k) where
  type Unit = L '[]
  type p ** q = L (UN L p ++ UN L q)
  withOb2 @(L as) @(L bs) = withIsList2 @as @bs
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = withOb2 @_ @as @bs (withOb2 @_ @(as ** bs) @cs (id @List))
  associatorInv @as @bs @cs = withOb2 @_ @bs @cs (withOb2 @_ @as @(bs ** cs) (id @List))