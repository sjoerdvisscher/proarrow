{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)
import Prelude (Show, ($), type (~))

import Proarrow.Category.Instance.Free
  ( Elem
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , WithShow
  )
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
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
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepUniv)
import Proarrow.Profunctor.Representable (CorepStar, Rep, RepCostar, Representable (..), repUniv)

infixl 8 **
infixl 7 ==

-- This is equal to a lax monoidal functor for representable profunctors
-- and to an oplax monoidal functor for corepresentable profunctors.
type MonoidalProfunctor :: forall {j} {k}. j +-> k -> Constraint
class (Monoidal j, Monoidal k, Profunctor p) => MonoidalProfunctor (p :: j +-> k) where
  one :: p Unit Unit
  (**) :: p x1 x2 -> p y1 y2 -> p (x1 ** y1) (x2 ** y2)

instance MonoidalProfunctor U.Unit where
  one = U.Unit
  U.Unit ** U.Unit = U.Unit

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :**: q) where
  one = one :**: one
  (f1 :**: f2) ** (g1 :**: g2) = (f1 ** g1) :**: (f2 ** g2)

par0Rep :: (Representable p, MonoidalProfunctor p) => Unit ~> p % Unit
par0Rep @p = index @p one

parRep :: (Representable p, MonoidalProfunctor p, Ob x, Ob y) => (p % x) ** (p % y) ~> p % (x ** y)
parRep @p @x @y = index @p (repUniv @p @x ** repUniv @p @y)

unpar0Corep :: (Corepresentable p, MonoidalProfunctor p) => p %% Unit ~> Unit
unpar0Corep @p = coindex @p one

unparCorep :: (Corepresentable p, MonoidalProfunctor p, Ob x, Ob y) => p %% (x ** y) ~> (p %% x) ** (p %% y)
unparCorep @p @x @y = coindex @p (corepUniv @p @x ** corepUniv @p @y)

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
  rightUnitor :: (Ob (a :: k)) => a ** Unit ~> a
  rightUnitorInv :: (Ob (a :: k)) => a ~> a ** Unit
  associator :: (Ob (a :: k), Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)
  associatorInv :: (Ob (a :: k), Ob b, Ob c) => a ** (b ** c) ~> (a ** b) ** c

leftUnitorIso :: (Monoidal k, Ob (a :: k), Ob (a' :: k)) => Iso (Unit ** a) (Unit ** a') a a'
leftUnitorIso = iso leftUnitor leftUnitorInv

rightUnitorIso :: (Monoidal k, Ob (a :: k), Ob (a' :: k)) => Iso (a ** Unit) (a' ** Unit) a a'
rightUnitorIso = iso rightUnitor rightUnitorInv

associatorIso
  :: (Monoidal k, Ob (a :: k), Ob b, Ob c, Ob (a' :: k), Ob b', Ob c')
  => Iso ((a ** b) ** c) ((a' ** b') ** c') (a ** (b ** c)) (a' ** (b' ** c'))
associatorIso @k @a @b @c @a' @b' @c' = iso (associator @k @a @b @c) (associatorInv @k @a' @b' @c')

class (((a ** b) ** c) ~ (a ** (b ** c))) => StrictlyAssoc a b c
instance (((a ** b) ** c) ~ (a ** (b ** c))) => StrictlyAssoc a b c

-- | If your monoidal category is a strict monoidal category, add 'Strictly' to your 'Ob' constraint.
-- This will let GHC know that the unitors and associators are strict, so you won't have to provide proof of that.
-- You can use 'associatorDefault' as implementation for both 'associator' and 'associatorInv':
--
-- @
-- leftUnitor = id
-- leftUnitorInv = id
-- rightUnitor = id
-- rightUnitorInv = id
-- associator \@a \@b \@c = associatorDefault \@a \@b \@c
-- associatorInv \@a \@b \@c = associatorDefault \@a \@b \@c
-- @
type Strictly :: forall {k}. k -> Constraint
class (a ** Unit ~ a, Unit ** a ~ a, forall b c. (Ob b, Ob c) => StrictlyAssoc a b c) => Strictly (a :: k) where
  associatorDefault :: forall b c. (Monoidal k, Ob a, Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)

instance (a ** Unit ~ a, Unit ** a ~ a, forall b c. (Ob b, Ob c) => StrictlyAssoc a b c) => Strictly (a :: k) where
  associatorDefault @b @c = withOb2 @_ @b @c (withOb2 @_ @a @(b ** c) id)

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
  one = Op one
  Op l ** Op r = Op (l ** r)

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

(==) :: (CategoryOf k) => (a :: k) ~> b -> b ~> c -> a ~> c
f == g = g . f

obj2 :: forall {k} a b. (Monoidal k, Ob (a :: k), Ob b) => Obj (a ** b)
obj2 = obj @a ** obj @b

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
leftUnitorWith f = leftUnitor . (f ** obj @a)

leftUnitorInvWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => Unit ~> b -> a ~> b ** a
leftUnitorInvWith f = (f ** obj @a) . leftUnitorInv

rightUnitorWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => b ~> Unit -> a ** b ~> a
rightUnitorWith f = rightUnitor . (obj @a ** f)

rightUnitorInvWith :: forall {k} a b. (Monoidal k, Ob (a :: k)) => Unit ~> b -> a ~> a ** b
rightUnitorInvWith f = (obj @a ** f) . rightUnitorInv

unitObj :: (Monoidal k) => Obj (Unit :: k)
unitObj = one

first :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (a ** c) ~> (b ** c)
first f = f ** obj @c

second :: forall {k} c a b. (Monoidal k, Ob (c :: k)) => (a ~> b) -> (c ** a) ~> (c ** b)
second f = obj @c ** f

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
swap' f g = swap @k @a' @b' . (f ** g) \\ f \\ g

swapInner'
  :: (SymMonoidal k)
  => (a :: k) ~> a'
  -> b ~> b'
  -> c ~> c'
  -> d ~> d'
  -> ((a ** b) ** (c ** d)) ~> ((a' ** c') ** (b' ** d'))
swapInner' a b c d =
  associatorInv' (tgt a) (tgt c) (tgt b ** tgt d)
    . (a ** (associator' (tgt c) (tgt b) (tgt d) . (swap' b c ** d) . associatorInv' (src b) (src c) (src d)))
    . associator' (src a) (src b) (src c ** src d)

swapInner
  :: forall {k} a b c d. (SymMonoidal k, Ob (a :: k), Ob b, Ob c, Ob d) => ((a ** b) ** (c ** d)) ~> ((a ** c) ** (b ** d))
swapInner =
  withOb2 @k @b @d $
    withOb2 @k @c @d $
      associatorInv @k @a @c @(b ** d)
        . (obj @a ** (associator @k @c @b @d . (swap @k @b @c ** obj @d) . associatorInv @k @b @c @d))
        . associator @k @a @b @(c ** d)

swapFst
  :: forall {k} (a :: k) b c d. (SymMonoidal k, Ob a, Ob b, Ob c, Ob d) => (a ** b) ** (c ** d) ~> (c ** b) ** (a ** d)
swapFst = (swap @k @b @c ** obj2 @a @d) . swapInner @b @a @c @d . (swap @k @a @b ** obj2 @c @d)

swapSnd
  :: forall {k} a (b :: k) c d. (SymMonoidal k, Ob a, Ob b, Ob c, Ob d) => (a ** b) ** (c ** d) ~> (a ** d) ** (c ** b)
swapSnd = (obj2 @a @d ** swap @k @b @c) . swapInner @a @b @d @c . (obj2 @a @b ** swap @k @c @d)

swapOuter
  :: forall {k} a b c d. (SymMonoidal k, Ob (a :: k), Ob b, Ob c, Ob d) => ((a ** b) ** (c ** d)) ~> ((d ** b) ** (c ** a))
swapOuter = (obj2 @d @b ** swap @k @a @c) . swapFst @a @b @d @c . (obj2 @a @b ** swap @k @c @d)

data UnitRep :: () +-> k
instance (Monoidal k) => FunctorForRep (UnitRep :: () +-> k) where
  type UnitRep @ '() = Unit
  fmap U.Unit = unitObj
data MultRep :: (k, k) +-> k
instance (Monoidal k) => FunctorForRep (MultRep :: (k, k) +-> k) where
  type MultRep @ '(a, b) = a ** b
  fmap (f :**: g) = f ** g
type Tensor = Rep MultRep

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
  foldStructure _ Par0 = one
  foldStructure go (Par f g) = go f ** go g
  foldStructure @f _ (LeftUnitor @a) = withLowerOb @a @f leftUnitor
  foldStructure @f _ (LeftUnitorInv @a) = withLowerOb @a @f leftUnitorInv
  foldStructure @f _ (RightUnitor @a) = withLowerOb @a @f rightUnitor
  foldStructure @f _ (RightUnitorInv @a) = withLowerOb @a @f rightUnitorInv
  foldStructure @f _ (Associator @a @b @c') = withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c' @f (associator @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
  foldStructure @f _ (AssociatorInv @a @b @c') = withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c' @f (associatorInv @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
deriving instance (WithShow a) => Show (Struct Monoidal a b)

-- 'MonoidalProfunctor'/'Monoidal' are mutual superclasses of each other (via 'Monoidal'\'s own
-- 'MonoidalProfunctor ((~>) :: CAT k)' superclass), so each instance below directly requires the
-- other's concrete instance: without 'Monoidal (FREE cs p)' spelled out explicitly here, GHC's
-- superclass solver doesn't derive it on its own when building 'MonoidalProfunctor's dictionary
-- (and symmetrically for 'CategoryOf (FREE cs p)' below).
instance (Monoidal (FREE cs p), Monoidal `Elem` cs) => MonoidalProfunctor (Free :: CAT (FREE cs p)) where
  one = St Par0 Id
  f ** g = St (Par f g) Id \\ f \\ g
instance
  (CategoryOf (FREE cs p), MonoidalProfunctor ((~>) :: CAT (FREE cs p)), Monoidal `Elem` cs)
  => Monoidal (FREE cs p)
  where
  type Unit = UnitF
  type a ** b = a **! b
  withOb2 r = r
  leftUnitor = St LeftUnitor Id
  leftUnitorInv = St LeftUnitorInv Id
  rightUnitor = St RightUnitor Id
  rightUnitorInv = St RightUnitorInv Id
  associator = St Associator Id
  associatorInv = St AssociatorInv Id

instance (SymMonoidal `Elem` cs) => HasStructure cs p SymMonoidal where
  data Struct SymMonoidal i o where
    Swap :: (Ob a, Ob b) => Struct SymMonoidal (a **! b) (b **! a)
  foldStructure @f _ (Swap @a @b) = withLowerOb @a @f (withLowerOb @b @f (swap @_ @(Lower f a) @(Lower f b)))
deriving instance (WithShow a) => Show (Struct SymMonoidal a b)

-- Requires 'Monoidal (FREE cs p)' directly rather than the usual 'Ok cs p', for the same reason
-- as 'Closed (FREE cs p)' below: going through 'Ok cs p' bundles 'All cs (FREE cs p)', which
-- reflexively includes 'SymMonoidal (FREE cs p)' — this very instance — whenever 'SymMonoidal' is
-- in @cs@, and GHC can't tie that knot productively.
instance (Monoidal (FREE cs p), SymMonoidal `Elem` cs, Monoidal `Elem` cs) => SymMonoidal (FREE cs p) where
  swap = St Swap Id
