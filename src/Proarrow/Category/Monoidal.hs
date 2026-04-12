{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)
import Prelude (($))

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Obj
  , Profunctor (..)
  , Promonad (..)
  , UN
  , obj
  , src
  , tgt
  , type (+->)
  )
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Optic (Iso, iso)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), trivialCorep)
import Proarrow.Profunctor.Representable (CorepStar, RepCostar, Representable (..), trivialRep)
import Proarrow.Profunctor.Constant (review, view)

infixl 8 ||
infixl 7 ==

-- This is equal to a lax monoidal functor for representable profunctors
-- and to an oplax monoidal functor for corepresentable profunctors.
type MonoidalProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Monoidal j, Monoidal k, Profunctor p) => MonoidalProfunctor (p :: j +-> k) where
  par0 :: p Unit Unit
  par :: p x1 x2 -> p y1 y2 -> p (x1 ** y1) (x2 ** y2)

instance MonoidalProfunctor U.Unit where
  par0 = U.Unit
  U.Unit `par` U.Unit = U.Unit

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :**: q) where
  par0 = par0 :**: par0
  (f1 :**: f2) `par` (g1 :**: g2) = (f1 `par` g1) :**: (f2 `par` g2)

par0Rep :: (Representable p, MonoidalProfunctor p) => Unit ~> p % Unit
par0Rep @p = index @p par0

parRep :: (Representable p, MonoidalProfunctor p, Ob x, Ob y) => (p % x) ** (p % y) ~> p % (x ** y)
parRep @p @x @y = index @p (trivialRep @p @x `par` trivialRep @p @y)

unpar0Corep :: (Corepresentable p, MonoidalProfunctor p) => p %% Unit ~> Unit
unpar0Corep @p = coindex @p par0

unparCorep :: (Corepresentable p, MonoidalProfunctor p, Ob x, Ob y) => p %% (x ** y) ~> (p %% x) ** (p %% y)
unparCorep @p @x @y = coindex @p (trivialCorep @p @x `par` trivialCorep @p @y)

type StrongMonoidalRep p = (Representable p, MonoidalProfunctor p, MonoidalProfunctor (RepCostar p))

unpar0Rep :: (StrongMonoidalRep p) => p % Unit ~> Unit
unpar0Rep @p = unpar0Corep @(RepCostar p)

unparRep :: (StrongMonoidalRep p, Ob x, Ob y) => p % (x ** y) ~> (p % x) ** (p % y)
unparRep @p @x @y = unparCorep @(RepCostar p) @x @y

type StrongMonoidalCorep p = (Corepresentable p, MonoidalProfunctor p, MonoidalProfunctor (CorepStar p))

par0Corep :: (StrongMonoidalCorep p) => Unit ~> p %% Unit
par0Corep @p = par0Rep @(CorepStar p)

parCorep :: (StrongMonoidalCorep p, Ob x, Ob y) => (p %% x) ** (p %% y) ~> p %% (x ** y)
parCorep @p @x @y = parRep @(CorepStar p) @x @y

type Monoidal :: Kind -> Constraint
class (CategoryOf k, MonoidalProfunctor ((~>) :: CAT k), Ob (Unit :: k)) => Monoidal k where
  type Unit :: k
  type (a :: k) ** (b :: k) :: k
  withOb2 :: (Ob (a :: k), Ob b) => ((Ob (a ** b)) => r) -> r
  leftUnitor :: (Ob (a :: k)) => Unit ** a ~> a
  leftUnitorInv :: (Ob (a :: k)) => a ~> Unit ** a
  leftUnitorInv = review leftUnitorIso
  rightUnitor :: (Ob (a :: k)) => a ** Unit ~> a
  rightUnitorInv :: (Ob (a :: k)) => a ~> a ** Unit
  associator :: (Ob (a :: k), Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)
  associator @a @b @c = view (associatorIso @k @a @b @c @a @b @c)
  associatorInv :: (Ob (a :: k), Ob b, Ob c) => a ** (b ** c) ~> (a ** b) ** c
  associatorInv @a @b @c = review (associatorIso @k @a @b @c @a @b @c)

leftUnitorIso :: (Monoidal k, Ob (a :: k), Ob (a' :: k)) => Iso (Unit ** a) (Unit ** a') a a'
leftUnitorIso = iso leftUnitor leftUnitorInv

rightUnitorIso :: (Monoidal k, Ob (a :: k), Ob (a' :: k)) => Iso (a ** Unit) (a' ** Unit) a a'
rightUnitorIso = iso rightUnitor rightUnitorInv

associatorIso
  :: (Monoidal k, Ob (a :: k), Ob b, Ob c, Ob (a' :: k), Ob b', Ob c')
  => Iso ((a ** b) ** c) ((a' ** b') ** c') (a ** (b ** c)) (a' ** (b' ** c'))
associatorIso @k @a @b @c @a' @b' @c' = iso (associator @k @a @b @c) (associatorInv @k @a' @b' @c')

instance Monoidal () where
  type Unit = '()
  type '() ** '() = '()
  withOb2 @'() @'() r = r
  leftUnitor = U.Unit
  leftUnitorInv = U.Unit
  rightUnitor = U.Unit
  rightUnitorInv = U.Unit
  associator = U.Unit
  associatorInv = U.Unit

instance (Monoidal j, Monoidal k) => Monoidal (j, k) where
  type Unit = '(Unit, Unit)
  type '(a1, a2) ** '(b1, b2) = '(a1 ** b1, a2 ** b2)
  withOb2 @'(a1, a2) @'(b1, b2) r = withOb2 @j @a1 @b1 (withOb2 @k @a2 @b2 r)
  leftUnitor @'(a1, a2) = leftUnitor @j @a1 :**: leftUnitor @k @a2
  leftUnitorInv @'(a1, a2) = leftUnitorInv @j @a1 :**: leftUnitorInv @k @a2
  rightUnitor @'(a1, a2) = rightUnitor @j @a1 :**: rightUnitor @k @a2
  rightUnitorInv @'(a1, a2) = rightUnitorInv @j @a1 :**: rightUnitorInv @k @a2
  associator @'(a1, a2) @'(b1, b2) @'(c1, c2) = associator @j @a1 @b1 @c1 :**: associator @k @a2 @b2 @c2
  associatorInv @'(a1, a2) @'(b1, b2) @'(c1, c2) = associatorInv @j @a1 @b1 @c1 :**: associatorInv @k @a2 @b2 @c2

instance (MonoidalProfunctor p) => MonoidalProfunctor (Op p) where
  par0 = Op par0
  Op l `par` Op r = Op (l `par` r)

-- | The opposite of a monoidal category is also monoidal, with the same tensor product.
instance (Monoidal k) => Monoidal (OPPOSITE k) where
  type Unit = OP Unit
  type a ** b = OP (UN OP a ** UN OP b)
  withOb2 @(OP a) @(OP b) r = withOb2 @k @a @b r
  leftUnitor = Op leftUnitorInv
  leftUnitorInv = Op leftUnitor
  rightUnitor = Op rightUnitorInv
  rightUnitorInv = Op rightUnitor
  associator @(OP a) @(OP b) @(OP c) = Op (associatorInv @k @a @b @c)
  associatorInv @(OP a) @(OP b) @(OP c) = Op (associator @k @a @b @c)

instance (SymMonoidal k) => SymMonoidal (OPPOSITE k) where
  swap @(OP a) @(OP b) = Op (swap @k @b @a)

(||) :: (Monoidal k) => (a :: k) ~> b -> c ~> d -> a ** c ~> b ** d
(||) = par

(==) :: (CategoryOf k) => (a :: k) ~> b -> b ~> c -> a ~> c
f == g = g . f

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

type State a = Unit ~> a
type Costate a = a ~> Unit
type Scalar k = (Unit :: k) ~> Unit

class (Monoidal k) => SymMonoidal k where
  swap :: (Ob (a :: k), Ob b) => (a ** b) ~> (b ** a)

instance SymMonoidal () where
  swap = U.Unit

instance (SymMonoidal j, SymMonoidal k) => SymMonoidal (j, k) where
  swap @'(a1, a2) @'(b1, b2) = swap @j @a1 @b1 :**: swap @k @a2 @b2

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

data UnitRep :: () +-> k
instance (Monoidal k) => FunctorForRep (UnitRep :: () +-> k) where
  type UnitRep @ '() = Unit
  fmap U.Unit = unitObj
data MultRep :: (k, k) +-> k
instance (Monoidal k) => FunctorForRep (MultRep :: (k, k) +-> k) where
  type MultRep @ '(a, b) = a ** b
  fmap (f :**: g) = f `par` g