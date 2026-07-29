{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal.Strictified where

import Data.Kind (Constraint)
import Prelude (($), type (~))

import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , associator'
  , associatorInv'
  )
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault, obj)

infixl 8 ||
infixl 7 ==

(||) :: (Monoidal k) => (as :: [k]) ~> bs -> cs ~> ds -> (as ++ cs) ~> (bs ++ ds)
(||) = (**)

(==) :: (CategoryOf k) => ((a :: k) ~> b) -> (b ~> c) -> a ~> c
f == g = g . f

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

data SList as where
  SNil :: SList '[]
  SSing :: (Ob a) => SList '[a]
  SCons :: (Ob a, Ob as, Ob bs, as ~ b ': bs) => SList (a ': as)

class ((as ++ bs) ++ cs ~ as ++ (bs ++ cs)) => Assoc as bs cs
instance (as ++ (bs ++ cs) ~ (as ++ bs) ++ cs) => Assoc as bs cs

type IsList :: forall {k}. [k] -> Constraint
class (CategoryOf k, as ~ as ++ '[], forall bs cs. Assoc as bs cs) => IsList (as :: [k]) where
  sList :: SList as
  withIsList2 :: (IsList bs) => ((IsList (as ++ bs)) => r) -> r
  swap1 :: (Ob b, SymMonoidal k) => as ++ '[b] ~> b ': as
  swap1Inv :: (Ob b, SymMonoidal k) => b ': as ~> as ++ '[b]
  swap' :: (IsList (bs :: [k]), SymMonoidal k) => as ++ bs ~> bs ++ as
instance (CategoryOf k) => IsList ('[] :: [k]) where
  sList = SNil
  withIsList2 r = r
  swap1 = id
  swap1Inv = id
  swap' = id
instance (Ob (a :: k), CategoryOf k) => IsList '[a] where
  sList = SSing
  withIsList2 @bs r = case sList @bs of SNil -> r; SSing -> r; SCons -> r
  swap1 @b = Str (swap @k @a @b)
  swap1Inv @b = Str (swap @k @b @a)
  swap' @bs = swap1Inv @bs @a
instance (Ob (a1 :: k), IsList (a2 ': as), IsList as) => IsList (a1 ': a2 ': as) where
  sList = SCons
  withIsList2 @bs r = withIsList2 @(a2 ': as) @bs $ withIsList2 @as @bs r
  swap1 @b = case swap1 @(a2 ': as) @b of f -> (Str @[a1, b] @[b, a1] (swap @_ @a1 @b) ** obj @(a2 ': as)) . (obj @'[a1] ** f)
  swap1Inv @b = case swap1Inv @(a2 ': as) @b of f -> (obj @'[a1] ** f) . (Str @[b, a1] @[a1, b] (swap @_ @b @a1) ** obj @(a2 ': as))
  swap' @bs = case swap' @(a2 ': as) @bs of
    f -> associator @_ @bs @'[a1] @(a2 ': as) . (swap1Inv @bs @a1 ** obj @(a2 ': as)) . (obj @'[a1] ** f)

type family Fold (as :: [k]) :: k where
  Fold ('[] :: [k]) = Unit :: k
  Fold '[a] = a
  Fold (a ': as) = a ** Fold as

fold :: forall {k} as. (Monoidal k) => SList (as :: [k]) -> Fold as ~> Fold as
fold SNil = one
fold (SSing @a) = obj @a
fold (SCons @a @as') = obj @a ** fold (sList @as')

concatFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold as ** Fold bs ~> Fold (as ++ bs)
concatFold =
  let fbs = fold (sList @bs)
      h :: forall (cs :: [k]). SList cs -> (Fold cs ** Fold bs) ~> Fold (cs ++ bs)
      h SNil = leftUnitor \\ fbs
      h (SSing @c) = case sList @bs of
        SNil -> rightUnitor
        SSing -> obj @c ** fbs
        SCons -> obj @c ** fbs
      h (SCons @c @cs') = let c = obj @c; cs = sList @cs' in (c ** h cs) . associator' c (fold cs) fbs
  in h (sList @as)

splitFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold (as ++ bs) ~> (Fold as ** Fold bs)
splitFold =
  let fbs = fold (sList @bs)
      h :: forall cs. SList cs -> Fold (cs ++ bs) ~> Fold cs ** Fold bs
      h SNil = leftUnitorInv \\ fbs
      h (SSing @c) = case sList @bs of
        SNil -> rightUnitorInv
        SSing -> obj @c ** fbs
        SCons -> obj @c ** fbs
      h (SCons @c @cs') = let c = obj @c; cs = sList @cs' in associatorInv' c (fold cs) fbs . (c ** h cs)
  in h (sList @as)

type Strictified :: CAT [k]
data Strictified as bs where
  Str :: (Ob as, Ob bs) => {unStr :: Fold as ~> Fold bs} -> Strictified as bs

singleton :: (CategoryOf k) => (a :: k) ~> b -> '[a] ~> '[b]
singleton a = Str a \\ a

instance (Monoidal k) => Profunctor (Strictified :: CAT [k]) where
  dimap = dimapDefault
  r \\ Str f = r \\ f

instance (Monoidal k) => Promonad (Strictified :: CAT [k]) where
  id @as = Str (fold (sList @as))
  Str f . Str g = Str (f . g)

-- | The strictified monoidal category, making the unitors and associators identities.
instance (Monoidal k) => CategoryOf [k] where
  type (~>) = Strictified
  type Ob as = IsList as

instance (Monoidal k) => MonoidalProfunctor (Strictified :: CAT [k]) where
  one = id
  Str @as @bs f ** Str @cs @ds g =
    withOb2 @[k] @as @cs $
      withOb2 @[k] @bs @ds $
        Str (concatFold @bs @ds . (f ** g) . splitFold @as @cs)

-- | List concattenation as monoidal tensor.
instance (Monoidal k) => Monoidal [k] where
  type Unit = '[]
  type as ** bs = as ++ bs
  withOb2 @as @bs r = withIsList2 @as @bs r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = obj @as ** obj @bs ** obj @cs
  associatorInv @as @bs @cs = obj @as ** obj @bs ** obj @cs

instance (SymMonoidal k) => SymMonoidal [k] where
  swap @as @bs = swap' @as @bs

instance (SymMonoidal k, CopyDiscard k) => CopyDiscard [k] where
  copy @as0 = case sList @as0 of
    SNil -> id
    SSing @a -> Str @'[a] @'[a, a] copy
    SCons @a @as -> (obj @'[a] ** (associator @_ @as @'[a] @as . (swap @[k] @'[a] @as ** obj @as))) . (Str @'[a] @'[a, a] copy ** copy)
  discard @as = case sList @as of
    SNil -> id
    SSing @a -> Str @'[a] @'[] discard
    SCons @a -> Str @'[a] @'[] discard ** discard