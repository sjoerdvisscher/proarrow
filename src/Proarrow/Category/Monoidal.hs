{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)
import Prelude (($), type (~))

import Proarrow.Core (CAT, CategoryOf (..), Kind, Obj, Profunctor (..), Promonad (..), dimapDefault, obj, type (+->), tgt, src)

-- This is equal to a monoidal functor for Star
-- and to an oplax monoidal functor for Costar
type MonoidalProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Monoidal j, Monoidal k, Profunctor p) => MonoidalProfunctor (p :: j +-> k) where
  par0 :: p Unit Unit
  par :: p x1 x2 -> p y1 y2 -> p (x1 ** y1) (x2 ** y2)

type Monoidal :: Kind -> Constraint
class (CategoryOf k, MonoidalProfunctor ((~>) :: CAT k)) => Monoidal k where
  type Unit :: k
  type (a :: k) ** (b :: k) :: k
  leftUnitor :: Ob (a :: k) => Unit ** a ~> a
  leftUnitorInv :: Ob (a :: k) => a ~> Unit ** a
  rightUnitor :: Ob (a :: k) => a ** Unit ~> a
  rightUnitorInv :: Ob (a :: k) => a ~> a ** Unit
  associator :: (Ob (a :: k), Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)
  associatorInv :: (Ob (a :: k), Ob b, Ob c) => a ** (b ** c) ~> (a ** b) ** c

leftUnitor' :: Monoidal k => (a :: k) ~> b -> Unit ** a ~> b
leftUnitor' f = f . leftUnitor \\ f

leftUnitorInv' :: Monoidal k => (a :: k) ~> b -> a ~> Unit ** b
leftUnitorInv' f = leftUnitorInv . f \\ f

rightUnitor' :: Monoidal k => (a :: k) ~> b -> a ** Unit ~> b
rightUnitor' f = f . rightUnitor \\ f

rightUnitorInv' :: Monoidal k => (a :: k) ~> b -> a ~> b ** Unit
rightUnitorInv' f = rightUnitorInv . f \\ f

associator' :: forall {k} a b c. Monoidal k => Obj (a :: k) -> Obj b -> Obj c -> (a ** b) ** c ~> a ** (b ** c)
associator' a b c = associator @k @a @b @c \\ a \\ b \\ c

associatorInv' :: forall {k} a b c. Monoidal k => Obj (a :: k) -> Obj b -> Obj c -> a ** (b ** c) ~> (a ** b) ** c
associatorInv' a b c = associatorInv @k @a @b @c \\ a \\ b \\ c

unitObj :: Monoidal k => Obj (Unit :: k)
unitObj = par0

class (Monoidal k) => SymMonoidal k where
  swap' :: (a :: k) ~> a' -> b ~> b' -> (a ** b) ~> (b' ** a')

swap :: forall {k} a b. (SymMonoidal k, Ob (a :: k), Ob b) => (a ** b) ~> (b ** a)
swap = swap' (obj @a) (obj @b)

type TracedMonoidalProfunctor :: forall {k}. k +-> k -> Constraint
class (SymMonoidal k, Profunctor p) => TracedMonoidalProfunctor (p :: k +-> k) where
  {-# MINIMAL trace | trace' #-}
  trace :: forall u x y. (Ob x, Ob y, Ob u) => p (x ** u) (y ** u) -> p x y
  trace = trace' (obj @x) (obj @y) (obj @u)
  trace' :: (x :: k) ~> x' -> y ~> y' -> u ~> u' -> p (x' ** u') (y ** u) -> p x y'
  trace' @_ @_ @_ @_ @u x y u p = trace @_ @u (dimap (x `par` u) (y `par` src u) p) \\ x \\ y \\ u

class (TracedMonoidalProfunctor ((~>) :: CAT k), Monoidal k) => TracedMonoidal k
instance (TracedMonoidalProfunctor ((~>) :: CAT k), Monoidal k) => TracedMonoidal k

isObPar :: forall {k} a b r. (Monoidal k, Ob (a :: k), Ob b) => ((Ob (a ** b)) => r) -> r
isObPar r = r \\ (obj @a `par` obj @b)

first :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (a ** c) ~> (b ** c)
first f = f `par` obj @c

second :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (c ** a) ~> (c ** b)
second f = obj @c `par` f

swapInner'
  :: (SymMonoidal k) => (a :: k) ~> a' -> b ~> b' -> c ~> c' -> d ~> d' -> ((a ** b) ** (c ** d)) ~> ((a' ** c') ** (b' ** d'))
swapInner' a b c d =
  associatorInv' (tgt a) (tgt c) (tgt b `par` tgt d)
    . (a `par` (associator' (tgt c) (tgt b) (tgt d) . (swap' b c `par` d) . associatorInv' (src b) (src c) (src d)))
    . associator' (src a) (src b) (src c `par` src d)

swapInner
  :: forall {k} a b c d. (SymMonoidal k, Ob (a :: k), Ob b, Ob c, Ob d) => ((a ** b) ** (c ** d)) ~> ((a ** c) ** (b ** d))
swapInner = swapInner' (obj @a) (obj @b) (obj @c) (obj @d)

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

data SList as where
  Nil :: SList '[]
  Cons :: (Ob a, Ob as) => Obj a -> SList as -> SList (a ': as)

class ((as ++ bs) ++ cs ~ as ++ (bs ++ cs)) => Assoc as bs cs
instance (as ++ (bs ++ cs) ~ (as ++ bs) ++ cs) => Assoc as bs cs

type IsList :: forall {k}. [k] -> Constraint
class (CategoryOf k, as ~ as ++ '[], forall bs cs. (IsList bs, IsList cs) => Assoc as bs cs) => IsList (as :: [k]) where sList :: SList as
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
