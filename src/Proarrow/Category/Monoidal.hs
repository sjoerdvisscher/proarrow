{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)
import Prelude (($), Show, Eq)

import Proarrow.Category.Instance.Free
  ( Elem
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Ok
  , WithEq
  , WithShow
  )
import Proarrow.Core (CAT, CategoryOf (..), Kind, Obj, Profunctor (..), Promonad (..), obj, src, tgt, type (+->))

-- This is equal to a monoidal functor for Star
-- and to an oplax monoidal functor for Costar
type MonoidalProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Monoidal j, Monoidal k, Profunctor p) => MonoidalProfunctor (p :: j +-> k) where
  par0 :: p Unit Unit
  par :: p x1 x2 -> p y1 y2 -> p (x1 ** y1) (x2 ** y2)

type Monoidal :: Kind -> Constraint
class (CategoryOf k, MonoidalProfunctor ((~>) :: CAT k), Ob (Unit :: k)) => Monoidal k where
  type Unit :: k
  type (a :: k) ** (b :: k) :: k
  withOb2 :: (Ob (a :: k), Ob b) => ((Ob (a ** b)) => r) -> r
  leftUnitor :: (Ob (a :: k)) => Unit ** a ~> a
  leftUnitorInv :: (Ob (a :: k)) => a ~> Unit ** a
  rightUnitor :: (Ob (a :: k)) => a ** Unit ~> a
  rightUnitorInv :: (Ob (a :: k)) => a ~> a ** Unit
  associator :: (Ob (a :: k), Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)
  associatorInv :: (Ob (a :: k), Ob b, Ob c) => a ** (b ** c) ~> (a ** b) ** c

obj2 :: forall {k} a b. (Monoidal k, Ob (a :: k), Ob b) => Obj (a ** b)
obj2 = obj @a `par` obj @b

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

leftUnitorWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => b ~> Unit -> b ** a ~> a
leftUnitorWith f = leftUnitor . (f `par` obj @a)

leftUnitorInvWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => Unit ~> b -> a ~> b ** a
leftUnitorInvWith f = (f `par` obj @a) . leftUnitorInv

rightUnitorWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => b ~> Unit -> a ** b ~> a
rightUnitorWith f = rightUnitor . (obj @a `par` f)

rightUnitorInvWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => Unit ~> b -> a ~> a ** b
rightUnitorInvWith f = (obj @a `par` f) . rightUnitorInv

unitObj :: (Monoidal k) => Obj (Unit :: k)
unitObj = par0

first :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (a ** c) ~> (b ** c)
first f = f `par` obj @c

second :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (c ** a) ~> (c ** b)
second f = obj @c `par` f

class (Monoidal k) => SymMonoidal k where
  swap :: (Ob (a :: k), Ob b) => (a ** b) ~> (b ** a)

swap' :: forall {k} (a :: k) a' b b'. (SymMonoidal k) => a ~> a' -> b ~> b' -> (a ** b) ~> (b' ** a')
swap' f g = swap @k @a' @b' . (f `par` g) \\ f \\ g

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
swapInner =
  withOb2 @k @b @d $
    withOb2 @k @c @d $
      associatorInv @k @a @c @(b ** d)
        . (obj @a `par` (associator @k @c @b @d . (swap @k @b @c `par` obj @d) . associatorInv @k @b @c @d))
        . associator @k @a @b @(c ** d)

swapFst
  :: forall {k} (a :: k) b c d. (SymMonoidal k, Ob a, Ob b, Ob c, Ob d) => (a ** b) ** (c ** d) ~> (c ** b) ** (a ** d)
swapFst = (swap @k @b @c `par` obj2 @a @d) . swapInner @b @a @c @d . (swap @k @a @b `par` obj2 @c @d)

swapSnd
  :: forall {k} a (b :: k) c d. (SymMonoidal k, Ob a, Ob b, Ob c, Ob d) => (a ** b) ** (c ** d) ~> (a ** d) ** (c ** b)
swapSnd = (obj2 @a @d `par` swap @k @b @c) . swapInner @a @b @d @c . (obj2 @a @b `par` swap @k @c @d)

swapOuter
  :: forall {k} a b c d. (SymMonoidal k, Ob (a :: k), Ob b, Ob c, Ob d) => ((a ** b) ** (c ** d)) ~> ((d ** b) ** (c ** a))
swapOuter = (obj2 @d @b `par` swap @k @a @c) . swapFst @a @b @d @c . (obj2 @a @b `par` swap @k @c @d)

data family UnitF :: k
instance (Monoidal `Elem` cs) => IsFreeOb (UnitF :: FREE cs p) where
  type Lower f UnitF = Unit
  withLowerOb r = r
data family (**!) (a :: k) (b :: k) :: k
instance (Ob (a :: FREE cs p), Ob b, Monoidal `Elem` cs) => IsFreeOb (a **! b) where
  type Lower f (a **! b) = Lower f a ** Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withOb2 @_ @(Lower f a) @(Lower f b) r))
instance (Monoidal `Elem` cs) => HasStructure cs p Monoidal where
  data Struct Monoidal i o where
    Par0 :: Struct Monoidal UnitF UnitF
    Par :: a ~> b -> c ~> d -> Struct Monoidal (a **! c) (b **! d)
    LeftUnitor :: (Ob a) => Struct Monoidal (UnitF **! a) a
    LeftUnitorInv :: (Ob a) => Struct Monoidal a (UnitF **! a)
    RightUnitor :: (Ob a) => Struct Monoidal (a **! UnitF) a
    RightUnitorInv :: (Ob a) => Struct Monoidal a (a **! UnitF)
    Associator :: (Ob a, Ob b, Ob c) => Struct Monoidal ((a **! b) **! c) (a **! (b **! c))
    AssociatorInv :: (Ob a, Ob b, Ob c) => Struct Monoidal (a **! (b **! c)) ((a **! b) **! c)
  foldStructure _ Par0 = par0
  foldStructure go (Par f g) = go f `par` go g
  foldStructure @f _ (LeftUnitor @a) = withLowerOb @a @f leftUnitor
  foldStructure @f _ (LeftUnitorInv @a) = withLowerOb @a @f leftUnitorInv
  foldStructure @f _ (RightUnitor @a) = withLowerOb @a @f rightUnitor
  foldStructure @f _ (RightUnitorInv @a) = withLowerOb @a @f rightUnitorInv
  foldStructure @f _ (Associator @a @b @c') = withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c' @f (associator @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
  foldStructure @f _ (AssociatorInv @a @b @c') = withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c' @f (associatorInv @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
deriving instance (WithEq a) => Eq (Struct Monoidal a b)
deriving instance (WithShow a) => Show (Struct Monoidal a b)
instance (Ok cs p, Monoidal `Elem` cs) => MonoidalProfunctor (Free :: CAT (FREE cs p)) where
  par0 = Str Par0 Id
  f `par` g = Str (Par f g) Id \\ f \\ g
instance (Ok cs p, Monoidal `Elem` cs) => Monoidal (FREE cs p) where
  type Unit = UnitF
  type a ** b = a **! b
  withOb2 r = r
  leftUnitor = Str LeftUnitor Id
  leftUnitorInv = Str LeftUnitorInv Id
  rightUnitor = Str RightUnitor Id
  rightUnitorInv = Str RightUnitorInv Id
  associator = Str Associator Id
  associatorInv = Str AssociatorInv Id