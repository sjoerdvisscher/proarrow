{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal.Strictified where

import Data.Kind (Constraint)
import Prelude (($), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), associatorInv', associator')
import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), dimapDefault, obj)

infixl 8 ||
infixl 7 ==

(||) :: (Monoidal k) => (as :: [k]) ~> bs -> cs ~> ds -> (as ++ cs) ~> (bs ++ ds)
(||) = par

(==) :: (CategoryOf k) => ((a :: k) ~> b) -> (b ~> c) -> a ~> c
f == g = g . f

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

data SList as where
  Nil :: SList '[]
  Cons :: (Ob a, Ob as) => Obj a -> SList as -> SList (a ': as)

class ((as ++ bs) ++ cs ~ as ++ (bs ++ cs)) => Assoc as bs cs
instance (as ++ (bs ++ cs) ~ (as ++ bs) ++ cs) => Assoc as bs cs

type IsList :: forall {k}. [k] -> Constraint
class (CategoryOf k, as ~ as ++ '[], forall bs cs. Assoc as bs cs) => IsList (as :: [k]) where
  sList :: SList as
  withIsList2 :: IsList bs => (IsList (as ++ bs) => r) -> r
  swap1 :: (Ob b, SymMonoidal k) => as ++ '[b] ~> b ': as
  swap1Inv :: (Ob b, SymMonoidal k) => b ': as ~> as ++ '[b]
  swap' :: (IsList (bs :: [k]), SymMonoidal k) => as ++ bs ~> bs ++ as
instance (CategoryOf k) => IsList ('[] :: [k]) where
  sList = Nil
  withIsList2 r = r
  swap1 = id
  swap1Inv = id
  swap' = id
instance (Ob (a :: k), CategoryOf k) => IsList '[a] where
  sList = Cons (obj @a) Nil
  withIsList2 @bs r = case sList @bs of Nil -> r; Cons{} -> r
  swap1 @b = Str (swap @k @a @b)
  swap1Inv @b = Str (swap @k @b @a)
  swap' @bs = swap1Inv @bs @a
instance (Ob (a1 :: k), IsList (a2 ': as), IsList as) => IsList (a1 ': a2 ': as) where
  sList = Cons (obj @a1) (sList @(a2 ': as))
  withIsList2 @bs r = withIsList2 @(a2 ': as) @bs $ withIsList2 @as @bs r
  swap1 @b = case swap1 @(a2 ': as) @b of f -> (Str @[a1, b] @[b, a1] (swap @_ @a1 @b) `par` obj @(a2 ': as)) . (obj @'[a1] `par` f)
  swap1Inv @b = case swap1Inv @(a2 ': as) @b of f -> (obj @'[a1] `par` f) . (Str @[b, a1] @[a1, b] (swap @_ @b @a1) `par` obj @(a2 ': as))
  swap' @bs = case swap' @(a2 ': as) @bs of f -> associator @_ @bs @'[a1] @(a2 ': as) . (swap1Inv @bs @a1 `par` obj @(a2 ': as)) . (obj @'[a1] `par` f)

type family Fold (as :: [k]) :: k where
  Fold ('[] :: [k]) = Unit :: k
  Fold '[a] = a
  Fold (a ': as) = a ** Fold as

fold :: forall {k} as. (Monoidal k) => SList (as :: [k]) -> Fold as ~> Fold as
fold Nil = par0
fold (Cons f Nil) = f
fold (Cons f fs@Cons{}) = f `par` fold fs

concatFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold as ** Fold bs ~> Fold (as ++ bs)
concatFold =
  let fbs = fold (sList @bs)
      h :: forall (cs :: [k]). SList cs -> (Fold cs ** Fold bs) ~> Fold (cs ++ bs)
      h Nil = leftUnitor \\ fbs
      h (Cons c Nil) = case sList @bs of
        Nil -> rightUnitor
        Cons{} -> c `par` fbs
      h (Cons c cs@Cons{}) = (c `par` h cs) . associator' c (fold cs) fbs
  in h (sList @as)

splitFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold (as ++ bs) ~> (Fold as ** Fold bs)
splitFold =
  let fbs = fold (sList @bs)
      h :: forall cs. SList cs -> Fold (cs ++ bs) ~> Fold cs ** Fold bs
      h Nil = leftUnitorInv \\ fbs
      h (Cons c Nil) = case sList @bs of
        Nil -> rightUnitorInv
        Cons{} -> c `par` fbs
      h (Cons c cs@Cons{}) = associatorInv' c (fold cs) fbs . (c `par` h cs)
  in h (sList @as)

type Strictified :: CAT [k]
data Strictified as bs where
  Str :: (Ob as, Ob bs) => Fold as ~> Fold bs -> Strictified as bs

singleton :: (CategoryOf k) => (a :: k) ~> b -> '[a] ~> '[b]
singleton a = Str a \\ a

asObj :: (Monoidal k) => SList (as :: [k]) -> Obj as
asObj Nil = obj
asObj (Cons a as) = singleton a `par` asObj as

instance (Monoidal k) => Profunctor (Strictified :: CAT [k]) where
  dimap = dimapDefault
  r \\ Str f = r \\ f

instance (Monoidal k) => Promonad (Strictified :: CAT [k]) where
  id :: forall (as :: [k]). (Ob as) => Strictified as as
  id = Str (fold (sList @as))
  Str f . Str g = Str (f . g)

instance (Monoidal k) => CategoryOf [k] where
  type (~>) = Strictified
  type Ob as = IsList as

instance (Monoidal k) => MonoidalProfunctor (Strictified :: CAT [k]) where
  par0 = id
  par :: (as :: [k]) ~> bs -> cs ~> ds -> as ++ cs ~> bs ++ ds
  par (Str @as @bs f) (Str @cs @ds g) =
    withOb2 @[k] @as @cs $
      withOb2 @[k] @bs @ds $
        Str (concatFold @bs @ds . (f `par` g) . splitFold @as @cs)

instance (Monoidal k) => Monoidal [k] where
  type Unit = '[]
  type as ** bs = as ++ bs
  withOb2 @as @bs r = withIsList2 @as @bs r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = obj @as `par` obj @bs `par` obj @cs
  associatorInv @as @bs @cs = obj @as `par` obj @bs `par` obj @cs

instance (SymMonoidal k) => SymMonoidal [k] where
  swap @as @bs = swap' @as @bs