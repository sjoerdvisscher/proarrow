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
  SNil :: List (L '[]) (L '[])
  SCons :: (Str.IsList as, Str.IsList bs) => a ~> b -> List (L as) (L bs) -> List (L (a ': as)) (L (b ': bs))

mkCons :: (CategoryOf k) => (a :: k) ~> b -> L as ~> L bs -> L (a ': as) ~> L (b ': bs)
mkCons f fs = SCons f fs \\ fs

instance (CategoryOf k) => CategoryOf (LIST k) where
  type (~>) = List
  type Ob as = (Is L as, Str.IsList (UN L as))

instance (CategoryOf k) => Promonad (List :: CAT (LIST k)) where
  id @(L bs) = case Str.sList @bs of
    Str.SNil -> SNil
    Str.SSing @a -> SCons (obj @a) SNil
    Str.SCons @a @as -> SCons (obj @a) (obj @(L as))
  SNil . SNil = SNil
  SCons f fs . SCons g gs = SCons (f . g) (fs . gs)

instance (CategoryOf k) => Profunctor (List :: CAT (LIST k)) where
  dimap = dimapDefault
  r \\ SNil = r
  r \\ SCons f SNil = r \\ f
  r \\ SCons f fs@SCons{} = r \\ f \\ fs

instance (CategoryOf k) => MonoidalProfunctor (List :: CAT (LIST k)) where
  par0 = SNil
  SNil `par` SNil = SNil
  SNil `par` gs@SCons{} = gs
  SCons f fs `par` SNil = mkCons f (fs `par` SNil)
  SCons f fs `par` SCons g gs = mkCons f (fs `par` SCons g gs)

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