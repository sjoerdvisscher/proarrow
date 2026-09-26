{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Monoidal categories, as kinds with a tensor: 'Monoidal' provides 'Unit', the tensor @('**')@,
-- and the unitor and associator isomorphisms; 'SymMonoidal' adds the symmetry 'swap'. A
-- 'MonoidalProfunctor' is a lax monoidal profunctor with 'one' and a value-level @('**')@, and a
-- category is 'Monoidal' if and only if its hom-profunctor is.
module Proarrow.Category.Monoidal where

import Data.Kind (Constraint)
import Data.Type.Nat (Nat (..), SNat (..), SNatI, snat)
import Prelude (Show, ($), type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Free
  ( Elem (..)
  , Elems
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Lower
  , WithShow
  , withLowerOb
  )
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product (Fst, Snd, (:**:) (..))
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
import Proarrow.Optic (PIso, iso)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), corepUniv)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Identity qualified as Id
import Proarrow.Profunctor.Representable (CorepStar, Rep, RepCostar, Representable (..), repUniv)
import Proarrow.Tools.Laws (Inverses (..), Law (..), Laws (..), inverses, (===))

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

instance (Monoidal k) => MonoidalProfunctor (Id.Id :: k +-> k) where
  one = Id.Id one
  Id.Id f ** Id.Id g = Id.Id (f ** g)

instance (MonoidalProfunctor p, MonoidalProfunctor q) => MonoidalProfunctor (p :.: q) where
  one = one :.: one
  (p :.: q) ** (r :.: s) = (p ** r) :.: (q ** s)

-- | A representable profunctor that is a 'MonoidalProfunctor': its functor @p '%'@ is /lax/
-- monoidal, splitting as 'par0Rep' and 'parRep'.
type LaxMonoidal p = (MonoidalProfunctor p, Representable p)

par0Rep :: (LaxMonoidal p) => Unit ~> p % Unit
par0Rep @p = index @p one

parRep :: (LaxMonoidal p, Ob x, Ob y) => (p % x) ** (p % y) ~> p % (x ** y)
parRep @p @x @y = index @p (repUniv @p @x ** repUniv @p @y)

-- | A corepresentable profunctor that is a 'MonoidalProfunctor': its functor @p '%%'@ is /oplax/
-- monoidal, splitting as 'unpar0Corep' and 'unparCorep'.
type OplaxMonoidal p = (MonoidalProfunctor p, Corepresentable p)

unpar0Corep :: (OplaxMonoidal p) => p %% Unit ~> Unit
unpar0Corep @p = coindex @p one

unparCorep :: (OplaxMonoidal p, Ob x, Ob y) => p %% (x ** y) ~> (p %% x) ** (p %% y)
unparCorep @p @x @y = coindex @p (corepUniv @p @x ** corepUniv @p @y)

-- | A __representable__ profunctor whose functor @p '%'@ is /oplax/ monoidal. Stating the oplax
-- structure of a representable functor means naming that same functor in its other variance, as
-- 'RepCostar' does. So the postfix here says which presentation @p@ is in, not which structure it
-- carries. Weaker than 'StrongMonoidalRep', which additionally asks @p@ itself to be
-- 'LaxMonoidal'.
type OplaxMonoidalRep p = (Representable p, OplaxMonoidal (RepCostar p))

unpar0Rep :: (OplaxMonoidalRep p) => p % Unit ~> Unit
unpar0Rep @p = unpar0Corep @(RepCostar p)

unparRep :: (OplaxMonoidalRep p, Ob x, Ob y) => p % (x ** y) ~> (p % x) ** (p % y)
unparRep @p @x @y = unparCorep @(RepCostar p) @x @y

-- | A __corepresentable__ profunctor whose functor @p '%%'@ is /lax/ monoidal, dually through
-- 'CorepStar'.
type LaxMonoidalCorep p = (Corepresentable p, LaxMonoidal (CorepStar p))

par0Corep :: (LaxMonoidalCorep p) => Unit ~> p %% Unit
par0Corep @p = par0Rep @(CorepStar p)

parCorep :: (LaxMonoidalCorep p, Ob x, Ob y) => (p %% x) ** (p %% y) ~> p %% (x ** y)
parCorep @p @x @y = parRep @(CorepStar p) @x @y

-- | A representable profunctor whose functor is /strong/ monoidal: lax as it stands, and oplax in
-- its other variance.
type StrongMonoidalRep p = (LaxMonoidal p, OplaxMonoidalRep p)

-- | A corepresentable profunctor whose functor is /strong/ monoidal, dually.
type StrongMonoidalCorep p = (OplaxMonoidal p, LaxMonoidalCorep p)

-- | A monoidal category: a tensor @'**'@ with a 'Unit', associative and unital up to the coherent
-- isomorphisms below. The tensor's action on arrows is the 'MonoidalProfunctor' method @**@ at
-- @('~>')@, which the superclass supplies.
--
-- __Laws:__
--
-- The three isomorphisms must be mutually inverse:
--
-- * @'leftUnitor' . 'leftUnitorInv' = 'id'@ and @'leftUnitorInv' . 'leftUnitor' = 'id'@
-- * @'rightUnitor' . 'rightUnitorInv' = 'id'@ and @'rightUnitorInv' . 'rightUnitor' = 'id'@
-- * @'associator' . 'associatorInv' = 'id'@ and @'associatorInv' . 'associator' = 'id'@
--
-- and natural in every argument:
--
-- * @'leftUnitor' . ('id' '**' f) = f . 'leftUnitor'@
-- * @'rightUnitor' . (f '**' 'id') = f . 'rightUnitor'@
-- * @'associator' . ((f '**' g) '**' h) = (f '**' (g '**' h)) . 'associator'@
--
-- subject to the two coherence conditions:
--
-- * Triangle: @('id' '**' 'leftUnitor') . 'associator' = 'rightUnitor' '**' 'id'@
-- * Pentagon: @('id' '**' 'associator') . 'associator' . ('associator' '**' 'id')
--   = 'associator' . 'associator'@
--
-- Checked by @Proarrow.Testing.Laws.testMonoidal@.
type Monoidal :: Kind -> Constraint
class (CategoryOf k, MonoidalProfunctor ((~>) :: CAT k), Ob (Unit :: k)) => Monoidal k where
  -- | The tensor unit.
  type Unit :: k

  -- | The tensor product of two objects.
  type (a :: k) ** (b :: k) :: k

  -- | Recovers @'Ob' (a '**' b)@ from the objecthood of the factors.
  withOb2 :: (Ob (a :: k), Ob b) => ((Ob (a ** b)) => r) -> r

  -- | Cancels a 'Unit' on the left.
  leftUnitor :: (Ob (a :: k)) => Unit ** a ~> a
  default leftUnitor :: (Ob (a :: k), (Unit ** a) ~ a) => Unit ** a ~> a
  leftUnitor = id

  -- | Introduces a 'Unit' on the left; inverse to 'leftUnitor'.
  leftUnitorInv :: (Ob (a :: k)) => a ~> Unit ** a
  default leftUnitorInv :: (Ob (a :: k), (Unit ** a) ~ a) => a ~> Unit ** a
  leftUnitorInv = id

  -- | Cancels a 'Unit' on the right.
  rightUnitor :: (Ob (a :: k)) => a ** Unit ~> a
  default rightUnitor :: (Ob (a :: k), (a ** Unit) ~ a) => a ** Unit ~> a
  rightUnitor = id

  -- | Introduces a 'Unit' on the right; inverse to 'rightUnitor'.
  rightUnitorInv :: (Ob (a :: k)) => a ~> a ** Unit
  default rightUnitorInv :: (Ob (a :: k), (a ** Unit) ~ a) => a ~> a ** Unit
  rightUnitorInv = id

  -- | Reassociates the tensor to the right.
  associator :: (Ob (a :: k), Ob b, Ob c) => (a ** b) ** c ~> a ** (b ** c)

  -- | Reassociates the tensor to the left; inverse to 'associator'.
  associatorInv :: (Ob (a :: k), Ob b, Ob c) => a ** (b ** c) ~> (a ** b) ** c

leftUnitorIso :: (Monoidal k, Ob (a :: k), Ob (a' :: k)) => PIso (Unit ** a) (Unit ** a') a a'
leftUnitorIso = iso leftUnitor leftUnitorInv

rightUnitorIso :: (Monoidal k, Ob (a :: k), Ob (a' :: k)) => PIso (a ** Unit) (a' ** Unit) a a'
rightUnitorIso = iso rightUnitor rightUnitorInv

associatorIso
  :: (Monoidal k, Ob (a :: k), Ob b, Ob c, Ob (a' :: k), Ob b', Ob c')
  => PIso ((a ** b) ** c) ((a' ** b') ** c') (a ** (b ** c)) (a' ** (b' ** c'))
associatorIso @k @a @b @c @a' @b' @c' = iso (associator @k @a @b @c) (associatorInv @k @a' @b' @c')

class (((a ** b) ** c) ~ (a ** (b ** c))) => StrictlyAssoc a b c
instance (((a ** b) ** c) ~ (a ** (b ** c))) => StrictlyAssoc a b c

-- | The @n@-fold tensor power of @x@: @x '**' x '**' … '**' x@, @n@ times, terminated by 'Unit'.
type family NFold (n :: Nat) (x :: k) :: k where
  NFold Z x = Unit
  NFold (S n) x = x ** NFold n x

-- | The 'Proarrow.Category.Monoidal.Strictified.Strictified' counterpart of 'NFold': @n@ copies
-- of @x@ as a list, rather than nested tensors.
type family NFoldS (n :: Nat) (x :: k) :: [k] where
  NFoldS Z x = '[]
  NFoldS (S n) x = x ': NFoldS n x

-- | @'NFold' n a@ is an object whenever @a@ is.
withObNFold :: forall {k} n (a :: k) r. (SNatI n, Ob a, Monoidal k) => ((Ob (NFold n a)) => r) -> r
withObNFold r = case snat @n of
  SZ -> r
  SS @n' -> withObNFold @n' @a (withOb2 @k @a @(NFold n' a) r)

-- | If your monoidal category is a strict monoidal category, add 'Strictly' to your 'Ob' constraint.
-- This will let GHC know that the unitors and associators are strict, so you won't have to provide proof of that.
--
-- The four unitors then default to 'id'. The defaults need only @'Unit' '**' a ~ a@ and
-- @a '**' 'Unit' ~ a@, so they also fire for a strictly unital category such as
-- 'Proarrow.Category.Instance.Mat.MatK' or 'Proarrow.Category.Instance.ZX.ZX'. Both associators
-- can use 'associatorDefault':
--
-- @
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

  -- a wildcard, not @'()@, so that @a ** b@ reduces for an abstract @a@, as on pairs
  type _ ** _ = '()
  withOb2 @'() @'() r = r
  leftUnitor = U.Unit
  leftUnitorInv = U.Unit
  rightUnitor = U.Unit
  rightUnitorInv = U.Unit
  associator = U.Unit
  associatorInv = U.Unit

instance (Monoidal j, Monoidal k) => Monoidal (j, k) where
  type Unit = '(Unit, Unit)

  -- Through the projections rather than by matching the pair, so that @a ** b@ reduces for an
  -- abstract @a@: the quantified @a ** b ~ a && b@ of 'Proarrow.Category.Monoidal.Cartesian.Cartesian'
  -- needs that.
  type a ** b = '(Fst @ a ** Fst @ b, Snd @ a ** Snd @ b)
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
  lowerOb @k' @_ r = fromAll @Monoidal @cs @k' r
data family (**!) (a :: k) (b :: k) :: k
instance (IsFreeOb (a :: FREE cs p), IsFreeOb b, Monoidal `Elem` cs) => IsFreeOb (a **! b) where
  type Lower f (a **! b) = Lower f a ** Lower f b
  lowerOb @k' @f r = fromAll @Monoidal @cs @k' (withLowerOb @f @a (withLowerOb @f @b (withOb2 @k' @(Lower f a) @(Lower f b) r)))
instance (Monoidal `Elem` cs) => HasStructure cs (p :: CAT k) Monoidal where
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
  foldStructure @f _ (LeftUnitor @a) = withLowerOb @f @a leftUnitor
  foldStructure @f _ (LeftUnitorInv @a) = withLowerOb @f @a leftUnitorInv
  foldStructure @f _ (RightUnitor @a) = withLowerOb @f @a rightUnitor
  foldStructure @f _ (RightUnitorInv @a) = withLowerOb @f @a rightUnitorInv
  foldStructure @f _ (Associator @a @b @c') = withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c' (associator @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
  foldStructure @f _ (AssociatorInv @a @b @c') = withLowerOb @f @a (withLowerOb @f @b (withLowerOb @f @c' (associatorInv @_ @(Lower f a) @(Lower f b) @(Lower f c'))))
instance (WithShow a) => Show (Struct Monoidal a b) where
  showsPrec _ Par0 = P.showString "one"
  showsPrec d (Par f g) = P.showParen (d P.> 8) $ P.showsPrec 9 f . P.showString " ** " . P.showsPrec 9 g
  showsPrec _ LeftUnitor = P.showString "leftUnitor"
  showsPrec _ LeftUnitorInv = P.showString "leftUnitorInv"
  showsPrec _ RightUnitor = P.showString "rightUnitor"
  showsPrec _ RightUnitorInv = P.showString "rightUnitorInv"
  showsPrec _ Associator = P.showString "associator"
  showsPrec _ AssociatorInv = P.showString "associatorInv"

instance (Monoidal `Elem` cs) => MonoidalProfunctor (Free :: CAT (FREE cs (p :: CAT k))) where
  one = St Par0 Nil
  f ** g = St (Par f g) Nil \\ f \\ g
instance (Monoidal `Elem` cs) => Monoidal (FREE cs (p :: CAT k)) where
  type Unit = UnitF
  type a ** b = a **! b
  withOb2 r = r
  leftUnitor = St LeftUnitor Nil
  leftUnitorInv = St LeftUnitorInv Nil
  rightUnitor = St RightUnitor Nil
  rightUnitorInv = St RightUnitorInv Nil
  associator = St Associator Nil
  associatorInv = St AssociatorInv Nil

-- | The structures the free category needs for 'SymMonoidal', and those its laws are stated for.
type SymMonoidalStructures :: [Kind -> Constraint]
type SymMonoidalStructures = '[Monoidal, SymMonoidal]

instance (SymMonoidalStructures `Elems` cs) => HasStructure cs (p :: CAT k) SymMonoidal where
  data Struct SymMonoidal i o where
    Swap :: (Ob a, Ob b) => Struct SymMonoidal (a **! b) (b **! a)
  foldStructure @f _ (Swap @a @b) = withLowerOb @f @a (withLowerOb @f @b (swap @_ @(Lower f a) @(Lower f b)))
instance Show (Struct SymMonoidal a b) where
  showsPrec _ Swap = P.showString "swap"

instance (SymMonoidalStructures `Elems` cs) => SymMonoidal (FREE cs (p :: CAT k)) where
  swap = St Swap Nil

-- | The tensor is a bifunctor, and the unitors and the associator are natural isomorphisms
-- satisfying the triangle and pentagon identities.
instance Laws '[Monoidal] where
  laws =
    inverses "leftUnitor" (\ @a -> Inverses (leftUnitor @_ @a) (leftUnitorInv @_ @a))
      P.++ inverses "rightUnitor" (\ @a -> Inverses (rightUnitor @_ @a) (rightUnitorInv @_ @a))
      P.++ inverses
        "associator"
        (\ @a @b @c -> Inverses (associator @_ @a @b @c) (associatorInv @_ @a @b @c))
      P.++ [ Law "tensor identity" \ @a @b _ -> withOb2 @_ @a @b (obj @a ** obj @b === id)
           , Law "tensor interchange" \ @a @b @c @d @e mor -> do
               f <- mor @a @b "f"
               g <- mor @b @c "g"
               h <- mor @d @e "h"
               i <- mor @e @c "i"
               (g . f) ** (i . h) === (g ** i) . (f ** h)
           , Law "leftUnitor naturality" \ @a @b mor -> do
               f <- mor @a @b "f"
               leftUnitor @_ @b . (one ** f) === f . leftUnitor @_ @a
           , Law "leftUnitorInv naturality" \ @a @b mor -> do
               f <- mor @a @b "f"
               leftUnitorInv @_ @b . f === (one ** f) . leftUnitorInv @_ @a
           , Law "rightUnitor naturality" \ @a @b mor -> do
               f <- mor @a @b "f"
               rightUnitor @_ @b . (f ** one) === f . rightUnitor @_ @a
           , Law "rightUnitorInv naturality" \ @a @b mor -> do
               f <- mor @a @b "f"
               rightUnitorInv @_ @b . f === (f ** one) . rightUnitorInv @_ @a
           , Law "associator naturality" \ @a @b @c @d mor -> do
               f <- mor @a @b "f"
               g <- mor @b @c "g"
               h <- mor @c @d "h"
               associator @_ @b @c @d . ((f ** g) ** h) === (f ** (g ** h)) . associator @_ @a @b @c
           , Law "associatorInv naturality" \ @a @b @c @d mor -> do
               f <- mor @a @b "f"
               g <- mor @b @c "g"
               h <- mor @c @d "h"
               associatorInv @_ @b @c @d . (f ** (g ** h)) === ((f ** g) ** h) . associatorInv @_ @a @b @c
           , Law "triangle identity" \ @a @b _ ->
               (obj @a ** leftUnitor @_ @b) . associator @_ @a @Unit @b === rightUnitor @_ @a ** obj @b
           , Law "pentagon identity" \ @a @b @c @d _ ->
               withOb2 @_ @a @b $
                 withOb2 @_ @b @c $
                   withOb2 @_ @c @d $
                     (obj @a ** associator @_ @b @c @d)
                       . associator @_ @a @(b ** c) @d
                       . (associator @_ @a @b @c ** obj @d)
                       === associator @_ @a @b @(c ** d)
                         . associator @_ @(a ** b) @c @d
           ]

-- | 'swap' is a natural self-inverse satisfying the hexagon identity.
instance Laws SymMonoidalStructures where
  laws =
    [ Law "swap self-inverse" \ @a @b _ -> (swap @_ @b @a . swap @_ @a @b === id) \\ swap @_ @a @b
    , Law "swap naturality" \ @a @b @c @d mor -> do
        f <- mor @a @c "f"
        g <- mor @b @d "g"
        swap @_ @c @d . (f ** g) === (g ** f) . swap @_ @a @b
    , Law "hexagon identity" \ @a @b @c _ ->
        withOb2 @_ @b @c $
          associator @_ @b @c @a
            . swap @_ @a @(b ** c)
            . associator @_ @a @b @c
            === (obj @b ** swap @_ @a @c)
              . associator @_ @b @a @c
              . (swap @_ @a @b ** obj @c)
    ]
