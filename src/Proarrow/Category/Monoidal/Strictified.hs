{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal.Strictified where

import Data.Kind (Constraint)
import Prelude (($), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Obj, Profunctor (..), Promonad (..), dimapDefault, obj)

infixl 7 ==

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
class (CategoryOf k, as ~ as ++ '[], Obs as, forall bs cs. Assoc as bs cs) => IsList (as :: [k]) where
  listCase
    :: ((as ~ '[]) => r)
    -> (forall a. (Ob a, as ~ '[a]) => r)
    -> (forall b bs c cs. (Ob b, Ob bs, Ob cs, as ~ (b ': bs), bs ~ (c ': cs)) => r)
    -> r
  sList :: SList as
  withIsList2 :: (IsList bs) => ((IsList (as ++ bs)) => r) -> r
  swap1 :: (Ob b, SymMonoidal k) => as ++ '[b] ~> b ': as
  swap1Inv :: (Ob b, SymMonoidal k) => b ': as ~> as ++ '[b]
  swap' :: (IsList (bs :: [k]), SymMonoidal k) => as ++ bs ~> bs ++ as
instance (CategoryOf k) => IsList ('[] :: [k]) where
  listCase n _ _ = n
  sList = SNil
  withIsList2 r = r
  swap1 = id
  swap1Inv = id
  swap' = id
instance (Ob (a :: k), CategoryOf k) => IsList '[a] where
  listCase _ s _ = s
  sList = SSing
  withIsList2 @bs r = listCase @bs r r r
  swap1 @b = Str (swap @k @a @b)
  swap1Inv @b = Str (swap @k @b @a)
  swap' @bs = swap1Inv @bs @a
instance (Ob (a1 :: k), IsList (a2 ': as), IsList as) => IsList (a1 ': a2 ': as) where
  listCase _ _ c = c
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

fold :: forall {k} (as :: [k]). (Monoidal k, Ob as) => Obj (Fold as)
fold = listCase @as one obj \ @b @bs -> obj @b ** fold @bs

withObFold :: forall {k} (as :: [k]) r. (Monoidal k, Ob as) => ((Ob (Fold as)) => r) -> r
withObFold r = listCase @as r r \ @b @bs -> withObFold @bs $ withOb2 @k @b @(Fold bs) r

type family Obs (as :: [k]) :: Constraint where
  Obs '[] = ()
  Obs (a ': as) = (Ob a, Obs as)

withObs :: forall {k} (as :: [k]) r. (Monoidal k, Ob as) => ((Obs as) => r) -> r
withObs r = listCase @as r r \ @_ @bs -> withObs @bs r

concatFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold as ** Fold bs ~> Fold (as ++ bs)
concatFold =
  let fbs = fold @bs
      h :: forall (cs :: [k]) r. (Ob cs) => ((Ob (Fold cs)) => Fold cs ** Fold bs ~> Fold (cs ++ bs) -> r) -> r
      h k =
        listCase @cs
          (k leftUnitor)
          (\ @c -> k $ listCase @bs rightUnitor (obj @c ** fbs) (obj @c ** fbs))
          (\ @c @cs' -> h @cs' \cbs -> withOb2 @k @c @(Fold cs') $ k $ (obj @c ** cbs) . associator @_ @c @(Fold cs') @(Fold bs))
          \\ fbs
  in h @as id

splitFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold (as ++ bs) ~> (Fold as ** Fold bs)
splitFold =
  let fbs = fold @bs
      h :: forall (cs :: [k]) r. (Ob cs) => ((Ob (Fold cs)) => Fold (cs ++ bs) ~> Fold cs ** Fold bs -> r) -> r
      h k =
        listCase @cs
          (k leftUnitorInv)
          (\ @c -> k $ listCase @bs rightUnitorInv (obj @c ** fbs) (obj @c ** fbs))
          (\ @c @cs' -> h @cs' \cbs -> withOb2 @k @c @(Fold cs') $ k $ associatorInv @_ @c @(Fold cs') @(Fold bs) . (obj @c ** cbs))
          \\ fbs
  in h @as id

type Strictified :: CAT [k]
data Strictified as bs where
  Str :: (Ob as, Ob bs) => {unStr :: Fold as ~> Fold bs} -> Strictified as bs

singleton :: (CategoryOf k) => (a :: k) ~> b -> '[a] ~> '[b]
singleton a = Str a \\ a

obj1 :: forall {k} (a :: k). (Monoidal k, Ob a) => Obj '[a]
obj1 = obj @'[a]

concatMany :: forall {k} (as :: [k]). (Ob as, Monoidal k) => as ~> '[Fold as]
concatMany = withObFold @as (Str id)

splitMany :: forall {k} (as :: [k]). (Ob as, Monoidal k) => '[Fold as] ~> as
splitMany = withObFold @as (Str id)

instance (Monoidal k) => Profunctor (Strictified :: CAT [k]) where
  dimap = dimapDefault
  r \\ Str{} = r

instance (Monoidal k) => Promonad (Strictified :: CAT [k]) where
  id @as = Str (fold @as)
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

swap2 :: forall {k} (a :: k) (b :: k). (SymMonoidal k, Ob a, Ob b) => '[a, b] ~> '[b, a]
swap2 = swap @[k] @'[a] @'[b]