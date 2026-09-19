{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Binary coproducts: 'HasBinaryCoproducts' provides @a '||' b@ with injections 'lft'\/'rgt' and
-- copairing @('|||')@, and 'HasCoproducts' adds the initial object. Also biproducts ('HasBiproducts')
-- and the 'COPROD' kind wrapper, which makes @('||')@ the tensor of a monoidal structure on the same
-- objects.
module Proarrow.Colimit.BinaryCoproduct where

import Data.Kind (Type)
import Prelude (Show, ($), type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free
  ( Elem (..)
  , FREE (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Lower
  , WithShow
  , withLowerOb
  )
import Proarrow.Category.Instance.Free qualified as F
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Product (Diag, (:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), UN, WrappedOb, type (+->))
import Proarrow.Functor (Functor (..), FunctorForRep (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), PROD (..), Prod (..), diag)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (Obj, obj, tgt)
import Proarrow.Profunctor.Corepresentable (Corepresentable (..), withObCorep)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Coproduct (coproduct, (:+:) (..))
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (CorepStar (..), Rep (..), Representable (..))

infixl 4 ||
infixl 4 |||
infixl 4 +++

-- | Binary coproducts, dual to 'Proarrow.Limit.BinaryProduct.HasBinaryProducts': an object
-- @a '||' b@ with injections 'lft' and 'rgt', universal among all pairs of arrows into a common
-- target -- each such pair factors through it uniquely via '(|||)'.
--
-- __Laws:__
--
-- * @(f '|||' g) . 'lft' = f@
-- * @(f '|||' g) . 'rgt' = g@
-- * Uniqueness: @(h . f) '|||' (h . g) = h . (f '|||' g)@
--
-- Checked by @Proarrow.Testing.Laws.propBinaryCoproducts@.
class (CategoryOf k) => HasBinaryCoproducts k where
  -- | The coproduct object.
  type (a :: k) || (b :: k) :: k

  -- | Recovers @'Ob' (a '||' b)@ from the objecthood of the summands.
  withObCoprod :: (Ob (a :: k), Ob b) => ((Ob (a || b)) => r) -> r

  -- | The left injection.
  lft :: (Ob (a :: k), Ob b) => a ~> (a || b)

  -- | The right injection.
  rgt :: (Ob (a :: k), Ob b) => b ~> (a || b)

  -- | The mediating arrow: case-splits two arrows into a common target.
  (|||) :: (x :: k) ~> a -> y ~> a -> (x || y) ~> a

  -- | The coproduct of two arrows, acting on each summand independently.
  (+++) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a || b ~> x || y
  l +++ r = lft @k @x @y . l ||| rgt @k @x @y . r \\ l \\ r

lft' :: forall {k} (a :: k) a' b. (HasBinaryCoproducts k) => a ~> a' -> Obj b -> a ~> (a' || b)
lft' a b = lft @k @a' @b . a \\ a \\ b

rgt' :: forall {k} (a :: k) b b'. (HasBinaryCoproducts k) => Obj a -> b ~> b' -> b ~> (a || b')
rgt' a b = rgt @k @a @b' . b \\ a \\ b

left :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryCoproducts k, Ob c) => a ~> b -> (a || c) ~> (b || c)
left f = f +++ obj @c

right :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryCoproducts k, Ob c) => a ~> b -> (c || a) ~> (c || b)
right f = obj @c +++ f

codiag :: forall {k} (a :: k). (HasBinaryCoproducts k, Ob a) => (a || a) ~> a
codiag = id ||| id

swapCoprod' :: forall {k} (a :: k) a' b b'. (HasBinaryCoproducts k) => a ~> a' -> b ~> b' -> (a || b) ~> (b' || a')
swapCoprod' a b = rgt' (tgt b) a ||| lft' b (tgt a)

swapCoprod :: forall {k} (a :: k) b. (HasBinaryCoproducts k, Ob a, Ob b) => a || b ~> b || a
swapCoprod = swapCoprod' (obj @a) (obj @b)

-- | The coproduct as a functor from the product category, @'(a, b) ↦ a || b@ -- the coproduct
-- analogue of 'Proarrow.Category.Monoidal.MultRep'.
data PlusRep :: (k, k) +-> k

instance (HasBinaryCoproducts k) => FunctorForRep (PlusRep :: (k, k) +-> k) where
  type PlusRep @ '(a, b) = a || b
  fmap (f :**: g) = f +++ g

data family Coproduct :: k -> k +-> k
instance (HasBinaryCoproducts k, Ob a) => FunctorForRep (Coproduct a :: k +-> k) where
  type Coproduct a @ b = a || b
  fmap f = right @a f

type HasCoproducts k = (HasInitialObject k, HasBinaryCoproducts k)

class ((a ** b) ~ (a || b)) => TensorIsCoproduct a b
instance ((a ** b) ~ (a || b)) => TensorIsCoproduct a b
class
  (HasCoproducts k, Monoidal k, (Unit :: k) ~ InitialObject, forall (a :: k) (b :: k). TensorIsCoproduct a b) =>
  Cocartesian k
instance
  (HasCoproducts k, Monoidal k, (Unit :: k) ~ InitialObject, forall (a :: k) (b :: k). TensorIsCoproduct a b)
  => Cocartesian k

-- | Every functor between cocartesian categories is lax monoidal, @f a || f b ~> f (a || b)@ by the
-- injections and @InitialObject ~> f InitialObject@ by initiality. On the 'CorepStar' of its
-- corepresentable profunctor this is 'Proarrow.Category.Monoidal.LaxMonoidal'.
instance (Corepresentable p, Cocartesian j, Cocartesian k) => MonoidalProfunctor (CorepStar (p :: j +-> k)) where
  one = withObCorep @p @Unit (CorepStar initiate)
  CorepStar @a f ** CorepStar @b g = withOb2 @k @a @b (CorepStar (parCorepCocartesian @p @a @b f g))

parCorepCocartesian
  :: forall {j} {k} p (a :: k) b a' b'
   . ( Corepresentable (p :: j +-> k)
     , Cocartesian j
     , Cocartesian k
     , TensorIsCoproduct a b
     , TensorIsCoproduct a' b'
     , Ob a
     , Ob b
     )
  => (a' ~> p %% a) -> (b' ~> p %% b) -> (a' ** b') ~> p %% (a ** b)
parCorepCocartesian f g = corepMap @p (lft @k @a @b) . f ||| corepMap @p (rgt @k @a @b) . g

instance HasBinaryCoproducts Type where
  type a || b = P.Either a b
  withObCoprod r = r
  lft = P.Left
  rgt = P.Right
  (|||) = P.either

instance HasBinaryCoproducts () where
  type '() || '() = '()
  withObCoprod r = r
  lft = U.Unit
  rgt = U.Unit
  U.Unit ||| U.Unit = U.Unit

instance HasBinaryCoproducts BOOL where
  type FLS || b = b
  type TRU || b = TRU
  type a || FLS = a
  type a || TRU = TRU
  withObCoprod @a r = case obj @a of
    Tru -> r
    Fls -> r
  lft @a @b = case obj @a of
    Fls -> initiate @_ @b
    Tru -> Tru
  rgt @a @b = case obj @b of
    Fls -> initiate @_ @a
    Tru -> Tru
  Fls ||| Fls = Fls
  F2T ||| b = b
  Tru ||| _ = Tru

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (j +-> k) where
  type p || q = p :+: q
  withObCoprod r = r
  lft = Prof InjL
  rgt = Prof InjR
  Prof l ||| Prof r = Prof (coproduct l r)

instance (HasBinaryCoproducts j, Corepresentable (p :: j +-> k), Corepresentable q) => Corepresentable (p :*: q) where
  type (p :*: q) %% a = (p %% a) || (q %% a)
  coindex (p :*: q) = coindex p ||| coindex q
  cotabulate @a f =
    withObCorep @p @a
      (withObCorep @q @a (cotabulate (f . lft @_ @(p %% a) @(q %% a)) :*: cotabulate (f . rgt @_ @(p %% a) @(q %% a))))
  corepMap f = corepMap @p f +++ corepMap @q f

instance (HasBinaryCoproducts k) => HasBinaryCoproducts (PROD k) where
  type PR a || PR b = PR (a || b)
  withObCoprod @(PR a) @(PR b) r = withObCoprod @k @a @b r
  lft @(PR a) @(PR b) = Prod (lft @_ @a @b)
  rgt @(PR a) @(PR b) = Prod (rgt @_ @a @b)
  Prod l ||| Prod r = Prod (l ||| r)

type data COPROD k = COPR k

-- | Lifts a profunctor to the 'COPROD'-wrapped kinds, where the monoidal structure is the
-- coproduct.
type Coprod :: j +-> k -> COPROD j +-> COPROD k
data Coprod p a b where
  Coprod :: {unCoprod :: p a b} -> Coprod p (COPR a) (COPR b)

instance (CategoryOf k) => Functor (COPR :: k -> COPROD k) where
  map = Coprod

instance (Profunctor p) => Profunctor (Coprod p) where
  dimap (Coprod l) (Coprod r) (Coprod p) = Coprod (dimap l r p)
  r \\ Coprod f = r \\ f
instance (Promonad p) => Promonad (Coprod p) where
  id = Coprod id
  Coprod f . Coprod g = Coprod (f . g)
instance (Representable p) => Representable (Coprod p) where
  type Coprod p % (COPR a) = COPR (p % a)
  index (Coprod p) = Coprod (index p)
  tabulate (Coprod f) = Coprod (tabulate f)
  repMap (Coprod f) = Coprod (repMap @p f)

instance
  (Profunctor f, Profunctor g, MonoidalProfunctor (Coprod f), MonoidalProfunctor (Coprod g))
  => MonoidalProfunctor (Coprod (f :.: g))
  where
  one = Coprod (nil :.: nil)
  Coprod (f :.: g) ** Coprod (h :.: i) = Coprod ((f ++ h) :.: (g ++ i))

-- | The same category as the category of @k@, but with coproducts as the tensor.
instance (CategoryOf k) => CategoryOf (COPROD k) where
  type (~>) = Coprod (~>)
  type Ob a = WrappedOb COPR a

instance (HasCoproducts k, cat ~ Hom k) => MonoidalProfunctor (Coprod cat :: COPROD k +-> COPROD k) where
  one = Coprod id
  Coprod f ** Coprod g = Coprod (f +++ g)

instance (HasCoproducts k) => MonoidalProfunctor (Coprod (Id :: k +-> k)) where
  one = Coprod (Id id)
  Coprod (Id f) ** Coprod (Id g) = Coprod (Id (f +++ g))

instance (HasCoproducts j, HasCoproducts k) => MonoidalProfunctor (Coprod (TerminalProfunctor :: j +-> k)) where
  one = Coprod TerminalProfunctor
  Coprod (TerminalProfunctor @a1 @b1) ** Coprod (TerminalProfunctor @a2 @b2) =
    withObCoprod @k @a1 @a2 $ withObCoprod @j @b1 @b2 $ Coprod TerminalProfunctor

nil :: (MonoidalProfunctor (Coprod p)) => p InitialObject InitialObject
nil = unCoprod one

(++) :: (MonoidalProfunctor (Coprod p)) => p a b -> p c d -> p (a || c) (b || d)
p ++ q = unCoprod (Coprod p ** Coprod q)

instance (HasInitialObject k) => HasInitialObject (COPROD k) where
  type InitialObject = COPR InitialObject
  initiate = Coprod initiate

instance (HasBinaryCoproducts k) => HasBinaryCoproducts (COPROD k) where
  type a || b = COPR (UN COPR a || UN COPR b)
  withObCoprod @(COPR a) @(COPR b) r = withObCoprod @k @a @b r
  lft @(COPR a) @(COPR b) = Coprod (lft @k @a @b)
  rgt @(COPR a) @(COPR b) = Coprod (rgt @k @a @b)
  Coprod f ||| Coprod g = Coprod (f ||| g)

instance (HasTerminalObject k) => HasTerminalObject (COPROD k) where
  type TerminalObject = COPR TerminalObject
  terminate = Coprod terminate

instance (HasBinaryProducts k) => HasBinaryProducts (COPROD k) where
  type COPR a && COPR b = COPR (a && b)
  withObProd @(COPR a) @(COPR b) r = withObProd @k @a @b r
  fst @(COPR a) @(COPR b) = Coprod (fst @k @a @b)
  snd @(COPR a) @(COPR b) = Coprod (snd @k @a @b)
  Coprod f &&& Coprod g = Coprod (f &&& g)

-- | Coproducts as monoidal tensor.
instance (HasCoproducts k) => Monoidal (COPROD k) where
  type Unit = COPR InitialObject
  type a ** b = COPR (UN COPR a || UN COPR b)
  withOb2 @(COPR a) @(COPR b) r = withObCoprod @k @a @b r
  leftUnitor = Coprod leftUnitorCoprod
  leftUnitorInv = Coprod leftUnitorCoprodInv
  rightUnitor = Coprod rightUnitorCoprod
  rightUnitorInv = Coprod rightUnitorCoprodInv
  associator @(COPR a) @(COPR b) @(COPR c) = Coprod (associatorCoprod @a @b @c)
  associatorInv @(COPR a) @(COPR b) @(COPR c) = Coprod (associatorCoprodInv @a @b @c)

leftUnitorCoprod :: forall {k} (a :: k). (HasCoproducts k, Ob a) => (InitialObject || a) ~> a
leftUnitorCoprod = initiate ||| id

leftUnitorCoprodInv :: forall {k} (a :: k). (HasCoproducts k, Ob a) => a ~> (InitialObject || a)
leftUnitorCoprodInv = rgt @k @InitialObject @a

rightUnitorCoprod :: forall {k} (a :: k). (HasCoproducts k, Ob a) => (a || InitialObject) ~> a
rightUnitorCoprod = id ||| initiate

rightUnitorCoprodInv :: forall {k} (a :: k). (HasCoproducts k, Ob a) => a ~> (a || InitialObject)
rightUnitorCoprodInv = lft @k @a @InitialObject

associatorCoprod :: forall {k} (a :: k) b c. (HasCoproducts k, Ob a, Ob b, Ob c) => (a || b) || c ~> a || (b || c)
associatorCoprod = (obj @a +++ lft @k @b @c) ||| withObCoprod @k @b @c (rgt @k @a @(b || c)) . rgt @k @b @c

associatorCoprodInv :: forall {k} (a :: k) b c. (HasCoproducts k, Ob a, Ob b, Ob c) => a || (b || c) ~> (a || b) || c
associatorCoprodInv = withObCoprod @k @a @b (lft @k @(a || b) @c) . lft @k @a @b ||| (rgt @k @a @b +++ obj @c)

instance (HasCoproducts k) => SymMonoidal (COPROD k) where
  swap @(COPR a) @(COPR b) = Coprod (swapCoprod @a @b)

-- | Inverse to 'Coprod': strips the 'COPR' wrappers from a profunctor between 'COPROD'-wrapped
-- kinds.
type Uncoprod :: (COPROD j +-> COPROD k) -> j +-> k
data Uncoprod p a b where
  Uncoprod :: p (COPR a) (COPR b) -> Uncoprod p a b

instance (Profunctor p, CategoryOf j, CategoryOf k) => Profunctor (Uncoprod p :: j +-> k) where
  dimap l r (Uncoprod p) = Uncoprod (dimap (Coprod l) (Coprod r) p \\ p)
  r \\ Uncoprod f = r \\ f

data family (+) (a :: k) (b :: k) :: k
instance (IsFreeOb (a :: FREE cs p), IsFreeOb b, HasBinaryCoproducts `Elem` cs) => IsFreeOb (a + b) where
  type Lower f (a + b) = Lower f a || Lower f b
  lowerOb @k' @f r =
    fromAll @HasBinaryCoproducts @cs @k'
      (withLowerOb @f @a (withLowerOb @f @b (withObCoprod @k' @(Lower f a) @(Lower f b) r)))
instance (HasBinaryCoproducts `Elem` cs) => HasStructure cs (p :: CAT k) HasBinaryCoproducts where
  data Struct HasBinaryCoproducts i o where
    Lft :: (Ob a, Ob b) => Struct HasBinaryCoproducts a (a + b)
    Rgt :: (Ob a, Ob b) => Struct HasBinaryCoproducts b (a + b)
    Sum :: a ~> o -> b ~> o -> Struct HasBinaryCoproducts (a + b) o
  foldStructure @f _ (Lft @a @b) = withLowerOb @f @a (withLowerOb @f @b (lft @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (Rgt @a @b) = withLowerOb @f @a (withLowerOb @f @b (rgt @_ @(Lower f a) @(Lower f b)))
  foldStructure go (Sum g h) = go g ||| go h
instance (WithShow a) => Show (Struct HasBinaryCoproducts a b) where
  showsPrec _ Lft = P.showString "lft"
  showsPrec _ Rgt = P.showString "rgt"
  showsPrec d (Sum f g) =
    P.showParen (d P.> 4) P.$
      P.showsPrec 5 f . P.showString " ||| " . P.showsPrec 5 g
instance (HasBinaryCoproducts `Elem` cs) => HasBinaryCoproducts (FREE cs (p :: CAT k)) where
  type a || b = a + b
  withObCoprod r = r
  lft = F.St Lft F.Nil
  rgt = F.St Rgt F.Nil
  f ||| g = F.St (Sum f g) F.Nil \\ f \\ g

class ((a && b) ~ (a || b)) => CheckBiproduct a b
instance ((a && b) ~ (a || b)) => CheckBiproduct a b

class
  (HasBinaryCoproducts k, HasBinaryProducts k, forall (a :: k) (b :: k). (Ob a, Ob b) => CheckBiproduct a b) =>
  HasBiproducts k
  where
  sum :: (a :: k) ~> b -> a ~> b -> a ~> b
  sum f g = codiag . (f +++ g) . diag \\ f \\ g

instance (HasBinaryCoproducts k) => HasBinaryProducts (OPPOSITE k) where
  type a && b = OP (UN OP a || UN OP b)
  withObProd @(OP a) @(OP b) r = withObCoprod @k @a @b r
  fst @(OP a) @(OP b) = Op (lft @_ @a @b)
  snd @(OP a) @(OP b) = Op (rgt @_ @a @b)
  Op a &&& Op b = Op (a ||| b)

instance (HasBinaryProducts k) => HasBinaryCoproducts (OPPOSITE k) where
  type a || b = OP (UN OP a && UN OP b)
  withObCoprod @(OP a) @(OP b) r = withObProd @k @a @b r
  lft @(OP a) @(OP b) = Op (fst @_ @a @b)
  rgt @(OP a) @(OP b) = Op (snd @_ @a @b)
  Op a ||| Op b = Op (a &&& b)

-- | The left adjoint to the diagonal functor.
instance (HasBinaryCoproducts k) => Corepresentable (Rep Diag :: k +-> (k, k)) where
  type Rep Diag %% '(a, b) = a || b
  coindex (Rep (f :**: g)) = f ||| g
  corepUniv @'(a, b) = withObCoprod @k @a @b (Rep (lft @k @a @b :**: rgt @k @a @b))
