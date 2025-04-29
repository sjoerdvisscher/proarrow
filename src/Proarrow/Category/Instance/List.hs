{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.List where

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Strictified qualified as Str
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, obj)

type data LIST k = L [k]
type instance UN L (L as) = as

type List :: CAT (LIST k)

-- | The free monoid in CAT
data List as bs where
  Nil :: List (L '[]) (L '[])
  Cons :: (Str.IsList as, Str.IsList bs) => a ~> b -> List (L as) (L bs) -> List (L (a ': as)) (L (b ': bs))

mkCons :: (CategoryOf k) => (a :: k) ~> b -> L as ~> L bs -> L (a ': as) ~> L (b ': bs)
mkCons f fs = Cons f fs \\ fs

instance (CategoryOf k) => CategoryOf (LIST k) where
  type (~>) = List
  type Ob as = (Is L as, Str.IsList (UN L as))

instance (CategoryOf k) => Promonad (List :: CAT (LIST k)) where
  id @(L bs) = case Str.sList @bs of
    Str.Nil -> Nil
    Str.Sing @a -> Cons (obj @a) Nil
    Str.Cons @a @as -> Cons (obj @a) (obj @(L as))
  Nil . Nil = Nil
  Cons f fs . Cons g gs = Cons (f . g) (fs . gs)

instance (CategoryOf k) => Profunctor (List :: CAT (LIST k)) where
  dimap = dimapDefault
  r \\ Nil = r
  r \\ Cons f Nil = r \\ f
  r \\ Cons f fs@Cons{} = r \\ f \\ fs

instance (CategoryOf k) => MonoidalProfunctor (List :: CAT (LIST k)) where
  par0 = Nil
  Nil `par` Nil = Nil
  Nil `par` gs@Cons{} = gs
  Cons f fs `par` Nil = mkCons f (fs `par` Nil)
  Cons f fs `par` Cons g gs = mkCons f (fs `par` Cons g gs)

instance (CategoryOf k) => Monoidal (LIST k) where
  type Unit = L '[]
  type p ** q = L (UN L p Str.++ UN L q)
  withOb2 @(L as) @(L bs) = Str.withIsList2 @as @bs
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = withOb2 @_ @as @bs (withOb2 @_ @(as ** bs) @cs (id @List))
  associatorInv @as @bs @cs = withOb2 @_ @bs @cs (withOb2 @_ @as @(bs ** cs) (id @List))