{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Core (CAT, CategoryOf (..), Obj, PRO, Profunctor (..), Promonad (..), dimapDefault, obj)
import Proarrow.Profunctor.Identity (Id (..))

class (CategoryOf k, Ob (Unit :: k)) => Monoidal k where
  type Unit :: k
  type (a :: k) ** (b :: k) :: k
  par :: ((a :: k) ~> b) -> (c ~> d) -> (a ** c) ~> (b ** d)
  leftUnitor :: (a :: k) ~> b -> Unit ** a ~> b
  leftUnitorInv :: (a :: k) ~> b -> a ~> Unit ** b
  rightUnitor :: (a :: k) ~> b -> a ** Unit ~> b
  rightUnitorInv :: (a :: k) ~> b -> a ~> b ** Unit
  associator :: Obj (a :: k) -> Obj b -> Obj c -> (a ** b) ** c ~> a ** (b ** c)
  associatorInv :: Obj (a :: k) -> Obj b -> Obj c -> a ** (b ** c) ~> (a ** b) ** c

class (Monoidal k) => SymMonoidal k where
  swap' :: Obj (a :: k) -> Obj b -> (a ** b) ~> (b ** a)

swap :: forall {k} a b. (SymMonoidal k, Ob (a :: k), Ob b) => (a ** b) ~> (b ** a)
swap = swap' (obj @a) (obj @b)

isObPar :: forall {k} a b r. (Monoidal k, Ob (a :: k), Ob b) => ((Ob (a ** b)) => r) -> r
isObPar r = r \\ (obj @a `par` obj @b)

first :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (a ** c) ~> (b ** c)
first f = f `par` obj @c

second :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (c ** a) ~> (c ** b)
second f = obj @c `par` f

swapInner
  :: (SymMonoidal k) => Obj (a :: k) -> Obj b -> Obj c -> Obj d -> ((a ** b) ** (c ** d)) ~> ((a ** c) ** (b ** d))
swapInner a b c d =
  associatorInv a c (b `par` d)
    . (a `par` (associator c b d . (swap' b c `par` d) . associatorInv b c d))
    . associator a b (c `par` d)

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

data SList as where
  Nil :: SList '[]
  Cons :: (Ob a, Ob as) => Obj a -> SList as -> SList (a ': as)

type IsList :: forall {k}. [k] -> Constraint
class (CategoryOf k) => IsList (as :: [k]) where sList :: SList as
instance (CategoryOf k) => IsList ('[] :: [k]) where sList = Nil
instance (Ob a, Ob as) => IsList (a ': as) where sList = Cons (obj @a) (sList @as)

type family Fold (as :: [k]) :: k where
  Fold ('[] :: [k]) = Unit :: k
  Fold '[a] = a
  Fold (a ': as) = a ** Fold as

fold :: forall {k} as. (Monoidal k) => SList (as :: [k]) -> Fold as ~> Fold as
fold Nil = id
fold (Cons f Nil) = f
fold (Cons f fs@Cons{}) = f `par` fold fs

concatFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold as ** Fold bs ~> Fold (as ++ bs)
concatFold =
  let fbs = fold (sList @bs)
      h :: forall (cs :: [k]). SList cs -> (Fold cs ** Fold bs) ~> Fold (cs ++ bs)
      h Nil = leftUnitor fbs
      h (Cons c Nil) = case sList @bs of
        Nil -> rightUnitor c
        Cons{} -> c `par` fbs
      h (Cons c cs@Cons{}) = (c `par` h cs) . associator c (fold cs) fbs
  in h (sList @as)

splitFold
  :: forall {k} (as :: [k]) (bs :: [k])
   . (Ob as, Ob bs, Monoidal k)
  => Fold (as ++ bs) ~> (Fold as ** Fold bs)
splitFold =
  let fbs = fold (sList @bs)
      h :: forall cs. SList cs -> Fold (cs ++ bs) ~> Fold cs ** Fold bs
      h Nil = leftUnitorInv fbs
      h (Cons c Nil) = case sList @bs of
        Nil -> rightUnitorInv c
        Cons{} -> c `par` fbs
      h (Cons c cs@Cons{}) = associatorInv c (fold cs) fbs . (c `par` h cs)
  in h (sList @as)

type Strictified :: CAT [k]
data Strictified as bs where
  Str :: (Ob as, Ob bs) => Fold as ~> Fold bs -> Strictified as bs

singleton :: (CategoryOf k) => Obj (a :: k) -> Obj '[a]
singleton a = Str a \\ a

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

instance (Monoidal k) => Monoidal [k] where
  type Unit = '[]
  type as ** bs = as ++ bs
  par :: (as :: [k]) ~> bs -> cs ~> ds -> as ++ cs ~> bs ++ ds
  par (Str @as @bs f) (Str @cs @ds g) =
    isObPar @as @cs $
      isObPar @bs @ds $
        Str (concatFold @bs @ds . (f `par` g) . splitFold @as @cs)
  leftUnitor a = a
  leftUnitorInv a = a
  rightUnitor :: forall (as :: [k]) bs. as ~> bs -> as ** Unit ~> bs
  rightUnitor f = f . go (sList @as) \\ f
    where
      go :: forall (cs :: [k]). SList cs -> cs ** Unit ~> cs
      go Nil = id
      go (Cons _ Nil) = id
      go (Cons a as@Cons{}) = singleton a `par` go as
  rightUnitorInv :: forall (as :: [k]) bs. as ~> bs -> as ~> bs ** Unit
  rightUnitorInv f = go (sList @bs) . f \\ f
    where
      go :: forall (cs :: [k]). SList cs -> cs ~> cs ** Unit
      go Nil = id
      go (Cons _ Nil) = id
      go (Cons a as@Cons{}) = singleton a `par` go as
  associator :: forall as bs cs. Obj (as :: [k]) -> Obj bs -> Obj cs -> (as ** bs) ** cs ~> as ** (bs ** cs)
  associator as' bs' cs' = go (sList @as) \\ as'
    where
      go :: forall (as' :: [k]). SList as' -> (as' ** bs) ** cs ~> as' ** (bs ** cs)
      go Nil = bs' `par` cs'
      go (Cons a Nil) = singleton a `par` (bs' `par` cs')
      go (Cons a as@Cons{}) = singleton a `par` go as
  associatorInv :: forall as bs cs. Obj (as :: [k]) -> Obj bs -> Obj cs -> as ** (bs ** cs) ~> (as ** bs) ** cs
  associatorInv as' bs' cs' = go (sList @as) \\ as'
    where
      go :: forall (as' :: [k]). SList as' -> as' ** (bs ** cs) ~> (as' ** bs) ** cs
      go Nil = bs' `par` cs'
      go (Cons a Nil) = singleton a `par` (bs' `par` cs')
      go (Cons a as@Cons{}) = singleton a `par` go as

-- instance SymMonoidal k => SymMonoidal [k] where
--   swap :: forall k (as :: [k]) (bs :: [k]). SymMonoidal k => Obj as -> Obj bs -> (as ** bs) ~> (bs ** as)
--   swap as bs = go (sList @as) (sList @bs) \\ as \\ bs
--     where
--       go :: forall (as' :: [k]) bs'. SList as' -> SList bs' -> (as' ** bs') ~> (bs' ** as')
--       go as Nil = rightUnitor _
--       go Nil bs = rightUnitorInv _
--       go (Cons a as) (Cons b bs) = _
--       swap1 :: Obj (a :: k) -> SList (as :: [k]) -> (a ': as) ~> (as ++ '[a])
--       swap1 = swap1

class (Monoidal j, Monoidal k, Profunctor p) => MonoidalProfunctor (p :: PRO j k) where
  lift0 :: p Unit Unit
  lift2 :: p x1 x2 -> p y1 y2 -> p (x1 ** y1) (x2 ** y2)

instance (Monoidal k) => MonoidalProfunctor (Id :: PRO k k) where
  lift0 = Id id
  lift2 (Id f) (Id g) = Id (f `par` g)

class (Monoidal j, Monoidal k, Profunctor p) => OplaxMonoidalProfunctor (p :: PRO j k) where
  unlift2 :: p (x1 ** y1) (x2 ** y2) -> (p x1 x2, p y1 y2)
