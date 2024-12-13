{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)

import Proarrow.Core (CAT, CategoryOf (..), Kind, Obj, Profunctor (..), Promonad (..), obj, src, tgt, type (+->))

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
  leftUnitor :: (Ob (a :: k)) => Unit ** a ~> a
  leftUnitorInv :: (Ob (a :: k)) => a ~> Unit ** a
  rightUnitor :: (Ob (a :: k)) => a ** Unit ~> a
  rightUnitorInv :: (Ob (a :: k)) => a ~> a ** Unit
  associator :: (Ob (a :: k), Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)
  associatorInv :: (Ob (a :: k), Ob b, Ob c) => a ** (b ** c) ~> (a ** b) ** c

leftUnitor' :: (Monoidal k) => (a :: k) ~> b -> Unit ** a ~> b
leftUnitor' f = f . leftUnitor \\ f

leftUnitorInv' :: (Monoidal k) => (a :: k) ~> b -> a ~> Unit ** b
leftUnitorInv' f = leftUnitorInv . f \\ f

rightUnitor' :: (Monoidal k) => (a :: k) ~> b -> a ** Unit ~> b
rightUnitor' f = f . rightUnitor \\ f

rightUnitorInv' :: (Monoidal k) => (a :: k) ~> b -> a ~> b ** Unit
rightUnitorInv' f = rightUnitorInv . f \\ f

associator' :: forall {k} a b c. (Monoidal k) => Obj (a :: k) -> Obj b -> Obj c -> (a ** b) ** c ~> a ** (b ** c)
associator' a b c = associator @k @a @b @c \\ a \\ b \\ c

associatorInv' :: forall {k} a b c. (Monoidal k) => Obj (a :: k) -> Obj b -> Obj c -> a ** (b ** c) ~> (a ** b) ** c
associatorInv' a b c = associatorInv @k @a @b @c \\ a \\ b \\ c

unitObj :: (Monoidal k) => Obj (Unit :: k)
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
  :: (SymMonoidal k)
  => (a :: k) ~> a'
  -> b ~> b'
  -> c ~> c'
  -> d ~> d'
  -> ((a ** b) ** (c ** d)) ~> ((a' ** c') ** (b' ** d'))
swapInner' a b c d =
  associatorInv' (tgt a) (tgt c) (tgt b `par` tgt d)
    . (a `par` (associator' (tgt c) (tgt b) (tgt d) . (swap' b c `par` d) . associatorInv' (src b) (src c) (src d)))
    . associator' (src a) (src b) (src c `par` src d)

swapInner
  :: forall {k} a b c d. (SymMonoidal k, Ob (a :: k), Ob b, Ob c, Ob d) => ((a ** b) ** (c ** d)) ~> ((a ** c) ** (b ** d))
swapInner = swapInner' (obj @a) (obj @b) (obj @c) (obj @d)
