{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal.Strictified where

import Data.Kind (Constraint)
import Prelude (($), type (~))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), associator', associatorInv', isObPar)
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
class (CategoryOf k, as ~ as ++ '[], forall bs cs. Assoc as bs cs) => IsList (as :: [k]) where sList :: SList as
instance (CategoryOf k) => IsList ('[] :: [k]) where sList = Nil
instance (Ob a, Ob as) => IsList (a ': as) where sList = Cons (obj @a) (sList @as)

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
    isObPar @as @cs $
      isObPar @bs @ds $
        Str (concatFold @bs @ds . (f `par` g) . splitFold @as @cs)

instance (Monoidal k) => Monoidal [k] where
  type Unit = '[]
  type as ** bs = as ++ bs
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor = id
  rightUnitorInv = id
  associator @as @bs @cs = obj @as `par` obj @bs `par` obj @cs
  associatorInv @as @bs @cs = obj @as `par` obj @bs `par` obj @cs

-- instance (SymMonoidal k) => SymMonoidal [k] where
--   swap' :: forall (as :: [k]) (bs :: [k]). (SymMonoidal k) => Obj as -> Obj bs -> (as ** bs) ~> (bs ** as)
--   swap' as bs = go (sList @as) (sList @bs) \\ as \\ bs
--     where
--       go :: forall (as' :: [k]) bs'. SList as' -> SList bs' -> (as' ** bs') ~> (bs' ** as')
--       go as' Nil = rightUnitor (asObj as')
--       go Nil bs' = rightUnitorInv (asObj bs')
--       go (Cons a as') (Cons b bs') =
--         let sa = singleton a; sb = singleton b; sas = asObj as'; sbs = asObj bs'
--         in (singleton b `par` (associator sbs sa sas . (swap1 a bs' `par` sas) . (singleton a `par` go as' bs')))
--             . (strSwap a b `par` (sas `par` sbs))
--             . (sa `par` ((swap1Inv b as' `par` sbs) . associatorInv sas sb sbs))
--       strSwap :: Obj (a :: k) -> Obj b -> '[a, b] ~> '[b, a]
--       strSwap a b = Str (swap' a b) \\ a \\ b
--       swap1 :: forall x xs. Obj (x :: k) -> SList (xs :: [k]) -> (x ': xs) ~> (xs ++ '[x])
--       swap1 = swap1
--       swap1Inv :: forall x xs. Obj (x :: k) -> SList (xs :: [k]) -> (xs ++ '[x]) ~> (x ': xs)
--       swap1Inv = swap1Inv
