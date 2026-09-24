{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Binary products: 'HasBinaryProducts' provides @a '&&' b@ with projections 'fst'\/'snd' and pairing
-- @('&&&')@, and 'HasProducts' adds the terminal object. Also 'Cartesian' (the monoidal tensor /is/ the
-- product) and the 'PROD' kind wrapper, which makes @('&&')@ the tensor of a monoidal structure on the
-- same objects.
module Proarrow.Limit.BinaryProduct where

import Data.Kind (Type)
import Prelude (Show, type (~))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (DecidableProfunctor (..), Decision (..))
import Proarrow.Category.Instance.Bool (BOOL (..), Booleans (..))
import Proarrow.Category.Instance.Free
  ( Elem (..)
  , FREE (..)
  , Free (..)
  , HasStructure (..)
  , IsFreeOb (..)
  , Lower
  , WithShow
  , withLowerOb
  )
import Proarrow.Category.Instance.Product (Diag, Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Hom, Profunctor (..), Promonad (..), UN, WrappedOb, type (+->))
import Proarrow.Functor (Functor (..), FunctorForRep (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (Obj, obj)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Product (prod, (:*:) (..))
import Proarrow.Profunctor.Representable (Representable (..), withObRep)

infixl 5 &&
infixl 5 &&&
infixl 5 ***

-- | Binary products: an object @a '&&' b@ with projections 'fst' and 'snd', universal among all
-- pairs of arrows out of a common source -- each such pair factors through it uniquely via '(&&&)'.
--
-- __Laws:__
--
-- * @'fst' . (f '&&&' g) = f@
-- * @'snd' . (f '&&&' g) = g@
-- * Uniqueness: @(f . h) '&&&' (g . h) = (f '&&&' g) . h@
--
-- Checked by @Proarrow.Testing.Laws.testBinaryProducts@.
class (CategoryOf k) => HasBinaryProducts k where
  -- | The product object.
  type (a :: k) && (b :: k) :: k

  -- | Recovers @'Ob' (a '&&' b)@ from the objecthood of the factors.
  withObProd :: (Ob (a :: k), Ob b) => ((Ob (a && b)) => r) -> r

  -- | The left projection.
  fst :: (Ob (a :: k), Ob b) => (a && b) ~> a

  -- | The right projection.
  snd :: (Ob (a :: k), Ob b) => (a && b) ~> b

  -- | The mediating arrow: pairs two arrows out of a common source.
  (&&&) :: (a :: k) ~> x -> a ~> y -> a ~> x && y

  -- | The product of two arrows, acting on each factor independently.
  (***) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a && b ~> x && y
  l *** r = (l . fst @k @a @b) &&& (r . snd @k @a @b) \\ l \\ r

fst' :: forall {k} (a :: k) a' b. (HasBinaryProducts k) => a ~> a' -> Obj b -> a && b ~> a'
fst' a b = a . fst @k @a @b \\ a \\ b

snd' :: forall {k} (a :: k) b b'. (HasBinaryProducts k) => Obj a -> b ~> b' -> a && b ~> b'
snd' a b = b . snd @k @a @b \\ a \\ b

first :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (a && c) ~> (b && c)
first f = f *** obj @c

second :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (c && a) ~> (c && b)
second f = obj @c *** f

diag :: forall {k} (a :: k). (HasBinaryProducts k, Ob a) => a ~> a && a
diag = id &&& id

data family Product :: k -> k +-> k
instance (HasBinaryProducts k, Ob a) => FunctorForRep (Product a :: k +-> k) where
  type Product a @ b = a && b
  fmap f = second @a f
instance (HasBinaryProducts k, Ob a) => Promonad (Corep (Product a) :: k +-> k) where
  id @b = Corep (snd @k @a @b)
  Corep f . Corep @c g = Corep (f . second @a g . associatorProd @a @a @c . first @c (diag @a))

type HasProducts k = (HasTerminalObject k, HasBinaryProducts k)

instance HasBinaryProducts Type where
  type a && b = (a, b)
  withObProd r = r
  fst = P.fst
  snd = P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts () where
  -- a wildcard, not @'()@, so that @a && b@ reduces for an abstract @a@, as on pairs
  type _ && _ = '()
  withObProd r = r
  fst = U.Unit
  snd = U.Unit
  U.Unit &&& U.Unit = U.Unit

instance HasBinaryProducts BOOL where
  type TRU && b = b
  type FLS && b = FLS
  type a && TRU = a
  type a && FLS = FLS
  withObProd @a r = case obj @a of
    Tru -> r
    Fls -> r
  fst @a @b = case obj @a of
    Fls -> Fls
    Tru -> terminate @_ @b
  snd @a @b = case obj @b of
    Fls -> Fls
    Tru -> terminate @_ @a
  Fls &&& _ = Fls
  F2T &&& b = b
  Tru &&& Tru = Tru

instance (HasBinaryProducts j, HasBinaryProducts k) => HasBinaryProducts (j, k) where
  -- Through the projections, as the tensor on pairs is, so that the two agree at abstract pairs.
  type a && b = '(Fst @ a && Fst @ b, Snd @ a && Snd @ b)
  withObProd @'(a1, a2) @'(b1, b2) r = withObProd @j @a1 @b1 (withObProd @k @a2 @b2 r)
  fst @'(a1, a2) @'(b1, b2) = fst @_ @a1 @b1 :**: fst @_ @a2 @b2
  snd @'(a1, a2) @'(b1, b2) = snd @_ @a1 @b1 :**: snd @_ @a2 @b2
  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)

instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (j +-> k) where
  type p && q = p :*: q
  withObProd r = r
  fst = Prof fstP
  snd = Prof sndP
  Prof l &&& Prof r = Prof (prod l r)

instance (HasBinaryProducts k, Representable (p :: j +-> k), Representable q) => Representable (p :*: q) where
  type (p :*: q) % a = (p % a) && (q % a)
  index (p :*: q) = index p &&& index q
  tabulate @b f =
    withObRep @p @b (withObRep @q @b (tabulate (fst @_ @(p % b) @(q % b) . f) :*: tabulate (snd @_ @(p % b) @(q % b) . f)))
  repMap f = repMap @p f *** repMap @q f

-- | A product holds when both components do: the type-level '&&' is 'BOOL'\'s categorical product.
instance (DecidableProfunctor p, DecidableProfunctor q) => DecidableProfunctor (p :**: q) where
  type Holds (p :**: q) '(a1, a2) '(b1, b2) = Holds p a1 b1 && Holds q a2 b2
  decide @'(a1, a2) @'(b1, b2) = case (decide @p @a1 @b1, decide @q @a2 @b2) of
    (Yes x, Yes y) -> Yes (x :**: y)
    (No, _) -> No
    (Yes _, No) -> No
  toHolds (f :**: g) r = toHolds f (toHolds g r)

instance (DecidableProfunctor p, DecidableProfunctor q) => DecidableProfunctor (p :*: q) where
  type Holds (p :*: q) a b = Holds p a b && Holds q a b
  decide @a @b = case (decide @p @a @b, decide @q @a @b) of
    (Yes x, Yes y) -> Yes (x :*: y)
    (No, _) -> No
    (Yes _, No) -> No
  toHolds (p :*: q) r = toHolds p (toHolds q r)

leftUnitorProd :: forall {k} (a :: k). (HasProducts k, Ob a) => TerminalObject && a ~> a
leftUnitorProd = snd @k @TerminalObject

leftUnitorProdInv :: forall {k} (a :: k). (HasProducts k, Ob a) => a ~> TerminalObject && a
leftUnitorProdInv = terminate &&& id

rightUnitorProd :: forall {k} (a :: k). (HasProducts k, Ob a) => a && TerminalObject ~> a
rightUnitorProd = fst @k @_ @TerminalObject

rightUnitorProdInv :: forall {k} (a :: k). (HasProducts k, Ob a) => a ~> a && TerminalObject
rightUnitorProdInv = id &&& terminate

associatorProd :: forall {k} (a :: k) b c. (HasBinaryProducts k, Ob a, Ob b, Ob c) => (a && b) && c ~> a && (b && c)
associatorProd = withObProd @k @a @b ((fst @k @a @b . fst @k @(a && b) @c) &&& (snd @k @a @b *** obj @c))

associatorProdInv :: forall {k} (a :: k) b c. (HasBinaryProducts k, Ob a, Ob b, Ob c) => a && (b && c) ~> (a && b) && c
associatorProdInv = withObProd @k @b @c ((obj @a *** fst @k @b @c) &&& (snd @k @b @c . snd @k @a @(b && c)))

swapProd :: forall {k} (a :: k) b. (HasBinaryProducts k, Ob a, Ob b) => a && b ~> b && a
swapProd = snd @k @a @b &&& fst @k @a @b

type data PROD k = PR k

-- | Lifts a profunctor to the 'PROD'-wrapped kinds, where the monoidal structure is the
-- categorical product.
type Prod :: j +-> k -> PROD j +-> PROD k
data Prod p (a :: PROD k) b where
  Prod :: {unProd :: p a b} -> Prod p (PR a) (PR b)

instance (CategoryOf k) => Functor (PR :: k -> PROD k) where
  map f = Prod f

instance (Profunctor p) => Profunctor (Prod p) where
  dimap (Prod l) (Prod r) (Prod p) = Prod (dimap l r p)
  r \\ Prod f = r \\ f
instance (Promonad p) => Promonad (Prod p) where
  id = Prod id
  Prod f . Prod g = Prod (f . g)

-- | The same category as the category of @k@, but with products as the tensor.
instance (CategoryOf k) => CategoryOf (PROD k) where
  type (~>) = Prod (~>)
  type Ob a = WrappedOb PR a

instance (Representable p) => Representable (Prod p) where
  type Prod p % PR a = PR (p % a)
  index (Prod p) = Prod (index p)
  tabulate (Prod f) = Prod (tabulate f)
  repMap (Prod f) = Prod (repMap @p f)

instance (HasTerminalObject k) => HasTerminalObject (PROD k) where
  type TerminalObject = PR TerminalObject
  terminate = Prod terminate
instance (HasBinaryProducts k) => HasBinaryProducts (PROD k) where
  type a && b = PR (UN PR a && UN PR b)
  withObProd @(PR a) @(PR b) r = withObProd @k @a @b r
  fst @(PR a) @(PR b) = Prod (fst @_ @a @b)
  snd @(PR a) @(PR b) = Prod (snd @_ @a @b)
  Prod f &&& Prod g = Prod (f &&& g)
  Prod f *** Prod g = Prod (f *** g)
instance (HasInitialObject k) => HasInitialObject (PROD k) where
  type InitialObject = PR InitialObject
  initiate = Prod initiate

instance (HasProducts k, cat ~ Hom k) => MonoidalProfunctor (Prod cat) where
  one = id
  f ** g = f *** g

-- | Products as monoidal structure.
instance (HasProducts k) => Monoidal (PROD k) where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 @(PR a) @(PR b) r = withObProd @k @a @b r
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @(PR a) @(PR b) @(PR c) = Prod (associatorProd @a @b @c)
  associatorInv @(PR a) @(PR b) @(PR c) = Prod (associatorProdInv @a @b @c)

instance (HasProducts k) => SymMonoidal (PROD k) where
  swap @(PR a) @(PR b) = Prod (swapProd @a @b)

type FromProd :: (k -> Type) -> (PROD k -> Type)
data FromProd f a where
  FromProd :: {unFromProd :: f a} -> FromProd f (PR a)

instance (Functor f) => Functor (FromProd f) where
  map (Prod g) (FromProd f) = FromProd (map g f)

instance MonoidalProfunctor (->) where
  one = id
  f ** g = f *** g

-- | Products as monoidal structure.
instance Monoidal Type where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 r = r
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal Type where
  swap = swapProd

instance MonoidalProfunctor Booleans where
  one = id
  f ** g = f *** g

-- | Products as monoidal structure.
instance Monoidal BOOL where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 @a @b = withObProd @BOOL @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @a @b @c = associatorProd @a @b @c
  associatorInv @a @b @c = associatorProdInv @a @b @c

instance SymMonoidal BOOL where
  swap @a @b = swapProd @a @b

data family (*!) (a :: k) (b :: k) :: k
instance (IsFreeOb (a :: FREE cs p), IsFreeOb b, HasBinaryProducts `Elem` cs) => IsFreeOb (a *! b) where
  type Lower f (a *! b) = Lower f a && Lower f b
  lowerOb @k' @f r =
    fromAll @HasBinaryProducts @cs @k' (withLowerOb @f @a (withLowerOb @f @b (withObProd @k' @(Lower f a) @(Lower f b) r)))
instance (HasBinaryProducts `Elem` cs) => HasStructure cs (p :: CAT k) HasBinaryProducts where
  data Struct HasBinaryProducts i o where
    Fst :: (Ob a, Ob b) => Struct HasBinaryProducts (a *! b) a
    Snd :: (Ob a, Ob b) => Struct HasBinaryProducts (a *! b) b
    Prd :: i ~> a -> i ~> b -> Struct HasBinaryProducts i (a *! b)
  foldStructure @f _ (Fst @a @b) = withLowerOb @f @a (withLowerOb @f @b (fst @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (Snd @a @b) = withLowerOb @f @a (withLowerOb @f @b (snd @_ @(Lower f a) @(Lower f b)))
  foldStructure go (Prd f g) = go f &&& go g
instance (WithShow a) => Show (Struct HasBinaryProducts a b) where
  showsPrec _ Fst = P.showString "fst"
  showsPrec _ Snd = P.showString "snd"
  showsPrec d (Prd f g) =
    P.showParen (d P.> 5) P.$
      P.showsPrec 6 f . P.showString " &&& " . P.showsPrec 6 g
instance (HasBinaryProducts `Elem` cs) => HasBinaryProducts (FREE cs (p :: CAT k)) where
  type a && b = a *! b
  withObProd r = r
  fst = St Fst Nil
  snd = St Snd Nil
  f &&& g = St (Prd f g) Nil \\ f \\ g

-- | The right adjoint to the diagonal functor.
instance (HasBinaryProducts k) => Representable (Corep Diag :: (k, k) +-> k) where
  type Corep Diag % '(a, b) = a && b
  index (Corep (f :**: g)) = f &&& g
  repUniv @'(a, b) = withObProd @k @a @b (Corep (fst @k @a @b :**: snd @k @a @b))
