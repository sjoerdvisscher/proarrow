{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Free where

import Data.Kind (Constraint, Type)
import Data.Typeable (Typeable, eqT, (:~:) (..))
import Prelude (Bool (..), Eq (..), Maybe (..), Show (..), (&&), (++))
import Prelude qualified as P

import Proarrow.Category.Instance.Discrete qualified as D
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core
  ( CAT
  , CategoryOf (..)
  , Kind
  , Profunctor (..)
  , Promonad (..)
  , UN
  , dimapDefault
  , type (+->)
  )
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Exponential (Closed (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Representable (..), dimapRep, withRepOb)
import Proarrow.Monoid (Mon(Mon), MONOIDK (..))

type family All (cs :: [Kind -> Constraint]) (k :: Kind) :: Constraint where
  All '[] k = ()
  All (c ': cs) k = (c k, All cs k)

class (All cs k => c k) => FromAll cs c k
instance (All cs k => c k) => FromAll cs c k

type Elem :: (Kind -> Constraint) -> [Kind -> Constraint] -> Constraint
class (forall k. FromAll cs c k) => c `Elem` cs
instance {-# OVERLAPPABLE #-} (c `Elem` cs) => c `Elem` (d ': cs)
instance c `Elem` (c ': cs)

newtype FREE (cs :: [Kind -> Constraint]) (p :: CAT j) = EMB j
type instance UN EMB (EMB a) = a

type Free :: CAT (FREE cs p)
data Free a b where
  Id :: (Ob a) => Free a a
  Emb :: (Ob a, Ob b, Typeable a, Typeable b) => p a b %1 -> Free (i :: FREE cs p) (EMB a) %1 -> Free i (EMB b)
  Str
    :: forall {j} {cs} {p :: CAT j} (c :: Kind -> Constraint) (a :: FREE cs p) b i
     . (c `Elem` cs, HasStructure cs p c, Ob a, Ob b)
    => Struct c a b %1 -> Free i a %1 -> Free i b

emb :: (Ob a, Ob b, Typeable a, Typeable b, Ok cs p) => p a b %1 -> Free (EMB a :: FREE cs p) (EMB b)
emb p = Emb p Id

class (forall x y. Eq (p x y)) => Eq2 p
instance (forall x y. Eq (p x y)) => Eq2 p

class (forall x y. P.Show (p x y)) => Show2 p
instance (forall x y. P.Show (p x y)) => Show2 p

class (Typeable p, Typeable cs, Typeable j, All cs (FREE cs p)) => Ok cs (p :: CAT j)
instance (Typeable p, Typeable cs, Typeable j, All cs (FREE cs p)) => Ok cs (p :: CAT j)

class (Ok c p, Eq2 p) => WithEq (a :: FREE c (p :: CAT j))
instance (Ok c p, Eq2 p) => WithEq (a :: FREE c (p :: CAT j))

instance (WithEq a) => Eq (Free a b) where
  Id == Id = True
  Emb @al p1 g1 == Emb @ar p2 g2 = case eqT @al @ar of Just Refl -> p1 == p2 && g1 == g2; Nothing -> False
  Str @strl @a1 s1 g1 == Str @strr @a2 s2 g2 = case (eqT @strl @strr, eqT @a1 @a2) of
    (Just Refl, Just Refl) -> s1 == s2 && g1 == g2
    _ -> False
  _ == _ = False

class (Show2 p) => WithShow (a :: FREE c (p :: CAT j))
instance (Show2 p) => WithShow (a :: FREE c (p :: CAT j))

instance (WithShow a) => Show (Free a b) where
  showsPrec _ Id = P.showString "id"
  showsPrec d (Emb p g) = showPostComp d p g
  showsPrec d (Str s g) = showPostComp d s g

showPostComp :: (Show p, WithShow a) => P.Int -> p -> Free a b -> P.ShowS
showPostComp d p Id = P.showsPrec d p
showPostComp d p g = P.showParen (d P.> 9) (P.showsPrec 10 p . P.showString " . " . P.showsPrec 10 g)

type IsFreeOb :: forall {j} {cs :: [Kind -> Constraint]} {p :: CAT j}. FREE cs p -> Constraint
class IsFreeOb (a :: FREE cs (p :: CAT j)) where
  type Lower (f :: j +-> k) (a :: FREE cs p) :: k
  withLowerOb :: forall {k} (f :: j +-> k) r . (Representable f, All cs k) => ((Ob (Lower f (a :: FREE cs p))) => r) -> r
instance (Ob a, Typeable a) => IsFreeOb (EMB a) where
  type Lower f (EMB a) = f % a
  withLowerOb @f r = withRepOb @f @a r

class ((Ok cs p, Eq2 p) => Eq2 str, (Ok cs p) => Typeable str, Show2 p => Show2 str) => CanEqShow (str :: CAT (FREE cs p))
instance ((Ok cs p, Eq2 p) => Eq2 str, (Ok cs p) => Typeable str, Show2 p => Show2 str) => CanEqShow (str :: CAT (FREE cs p))

class (Typeable c, CanEqShow (Struct c :: CAT (FREE cs p)), c `Elem` cs) => HasStructure cs (p :: CAT j) (c :: Kind -> Constraint) where
  data Struct c :: CAT (FREE cs p)
  foldStructure
    :: forall {k} (f :: j +-> k) (a :: FREE cs p) (b :: FREE cs p)
     . (All cs k, Representable f)
    => (forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y)
    -> Struct c a b
    -> Lower f a ~> Lower f b

fold
  :: forall {j} {k} {p :: CAT j} (cs :: [Kind -> Constraint]) (f :: j +-> k) (a :: FREE cs p) (b :: FREE cs p)
   . (All cs k, Representable f)
  => (forall x y. p x y -> (f % x) ~> (f % y))
  -> a ~> b
  -> Lower f a ~> Lower f b
fold pn = go
  where
    go :: forall (x :: FREE cs p) y. x ~> y -> Lower f x ~> Lower f y
    go Id = withLowerOb @x @f id
    go (Emb p g) = pn p . go g
    go (Str s g) = foldStructure @_ @_ @_ @_ @f go s . go g

retract
  :: forall {j} {k} cs (f :: j +-> k) a b. (All cs k, Representable f) => (a :: FREE cs InitialProfunctor) ~> b -> Lower f a ~> Lower f b
retract = fold @cs @f (\case {})

type ConstM :: k +-> MONOIDK m
data ConstM a b where
  ConstM :: (Ob b) => m -> ConstM (M :: MONOIDK m) b
instance (CategoryOf k, P.Monoid m) => Profunctor (ConstM :: k +-> MONOIDK m) where
  dimap l r (ConstM m) = ConstM m \\ l \\ r
  r \\ ConstM{} = r
instance (CategoryOf k, P.Monoid m) => Representable (ConstM :: k +-> MONOIDK m) where
  type ConstM % a = M
  index (ConstM m) = Mon (\() -> m)
  tabulate (Mon f) = ConstM (f ())
  repMap _ = id

foldConst :: forall {k} cs (p :: CAT k) m a b. (All cs (MONOIDK m), P.Monoid m, CategoryOf k) => (forall x y. p x y -> m) -> (a :: FREE cs p) ~> b -> m
foldConst f g = case fold @cs @ConstM (\p -> Mon (\() -> f p)) g of Mon m -> m ()

instance (Ok cs p) => CategoryOf (FREE cs p) where
  type (~>) = Free
  type Ob a = (IsFreeOb a, Typeable a)

instance (Ok cs p) => Promonad (Free :: CAT (FREE cs p)) where
  id = Id
  Id . g = g
  f . Id = f
  Emb p f . g = Emb p (f . g)
  Str s f . g = Str s (f . g)

instance (Ok cs p) => Profunctor (Free :: CAT (FREE cs p)) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Emb _ f = r \\ f
  r \\ Str _ f = r \\ f

data family TermF :: k
instance (HasTerminalObject `Elem` cs) => IsFreeOb (TermF :: FREE cs p) where
  type Lower f TermF = TerminalObject
  withLowerOb r = r
instance (HasTerminalObject `Elem` cs) => HasStructure cs p HasTerminalObject where
  data Struct HasTerminalObject a b where
    Terminal :: (Ob a) => Struct HasTerminalObject a TermF
  foldStructure @f _ (Terminal @a) = withLowerOb @a @f (terminate)
deriving instance Eq (Struct HasTerminalObject a b)
deriving instance Show (Struct HasTerminalObject a b)
instance (Ok cs p, HasTerminalObject `Elem` cs) => HasTerminalObject (FREE cs p) where
  type TerminalObject = TermF
  terminate = Str Terminal Id

data family InitF :: k
instance (HasInitialObject `Elem` cs) => IsFreeOb (InitF :: FREE cs p) where
  type Lower f InitF = InitialObject
  withLowerOb r = r
instance (HasInitialObject `Elem` cs) => HasStructure cs p HasInitialObject where
  data Struct HasInitialObject a b where
    Initial :: (Ob b) => Struct HasInitialObject InitF b
  foldStructure @f _ (Initial @b) = withLowerOb @b @f initiate
deriving instance Eq (Struct HasInitialObject a b)
deriving instance Show (Struct HasInitialObject a b)
instance (Ok cs p, HasInitialObject `Elem` cs) => HasInitialObject (FREE cs p) where
  type InitialObject = InitF
  initiate = Str Initial Id

data family (*!) (a :: k) (b :: k) :: k
instance (Ob (a :: FREE cs p), Ob b, HasBinaryProducts `Elem` cs) => IsFreeOb (a *! b) where
  type Lower f (a *! b) = Lower f a && Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withObProd @_ @(Lower f a) @(Lower f b) r))
instance (HasBinaryProducts `Elem` cs) => HasStructure cs p HasBinaryProducts where
  data Struct HasBinaryProducts i o where
    Fst :: (Ob a, Ob b) => Struct HasBinaryProducts (a *! b) a
    Snd :: (Ob a, Ob b) => Struct HasBinaryProducts (a *! b) b
    Prd :: i ~> a -> i ~> b -> Struct HasBinaryProducts i (a *! b)
  foldStructure @f _ (Fst @a @b) = withLowerOb @a @f (withLowerOb @b @f (fst @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (Snd @a @b) = withLowerOb @a @f (withLowerOb @b @f (snd @_ @(Lower f a) @(Lower f b)))
  foldStructure go (Prd f g) = go f &&& go g
deriving instance (WithEq a) => Eq (Struct HasBinaryProducts a b)
deriving instance (WithShow a) => Show (Struct HasBinaryProducts a b)
instance (Ok cs p, HasBinaryProducts `Elem` cs) => HasBinaryProducts (FREE cs p) where
  type a && b = a *! b
  withObProd r = r
  fst = Str Fst Id
  snd = Str Snd Id
  f &&& g = Str (Prd f g) Id \\ f \\ g

data family (+) (a :: k) (b :: k) :: k
instance (Ob (a :: FREE cs p), Ob b, HasBinaryCoproducts `Elem` cs) => IsFreeOb (a + b) where
  type Lower f (a + b) = Lower f a || Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withObCoprod @_ @(Lower f a) @(Lower f b) r))
instance (HasBinaryCoproducts `Elem` cs) => HasStructure cs p HasBinaryCoproducts where
  data Struct HasBinaryCoproducts i o where
    Lft :: (Ob a, Ob b) => Struct HasBinaryCoproducts a (a + b)
    Rgt :: (Ob a, Ob b) => Struct HasBinaryCoproducts b (a + b)
    Sum :: a ~> o -> b ~> o -> Struct HasBinaryCoproducts (a + b) o
  foldStructure @f _ (Lft @a @b) = withLowerOb @a @f (withLowerOb @b @f (lft @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (Rgt @a @b) = withLowerOb @a @f (withLowerOb @b @f (rgt @_ @(Lower f a) @(Lower f b)))
  foldStructure go (Sum g h) = (go g ||| go h)
deriving instance (WithEq a) => Eq (Struct HasBinaryCoproducts a b)
deriving instance (WithShow a) => Show (Struct HasBinaryCoproducts a b)
instance (Ok cs p, HasBinaryCoproducts `Elem` cs) => HasBinaryCoproducts (FREE cs p) where
  type a || b = a + b
  withObCoprod r = r
  lft = Str Lft Id
  rgt = Str Rgt Id
  f ||| g = Str (Sum f g) Id \\ f \\ g

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

data family (-->) (a :: k) (b :: k) :: k
instance (Ob (a :: FREE cs p), Ob b, Closed `Elem` cs, Monoidal `Elem` cs) => IsFreeOb (a --> b) where
  type Lower f (a --> b) = Lower f a ~~> Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withObExp @_ @(Lower f a) @(Lower f b) r))
instance (Closed `Elem` cs, Monoidal `Elem` cs) => HasStructure cs p Closed where
  data Struct Closed a b where
    Apply :: (Ob a, Ob b) => Struct Closed ((a --> b) **! a) b
    Curry :: forall a b c. (Ob a, Ob b) => (a **! b) ~> c -> Struct Closed a (b --> c)
  foldStructure @f _ (Apply @a @b) = withLowerOb @a @f (withLowerOb @b @f (apply @_ @(Lower f a) @(Lower f b)))
  foldStructure @f go (Curry @a @b f) = withLowerOb @a @f (withLowerOb @b @f (curry @_ @(Lower f a) @(Lower f b) (go f)))
deriving instance (WithEq a) => Eq (Struct Closed a b)
deriving instance (WithShow a) => Show (Struct Closed a b)
instance (Ok cs p, Closed `Elem` cs, Monoidal `Elem` cs) => Closed (FREE cs p) where
  type a ~~> b = a --> b
  withObExp r = r
  curry f = Str (Curry f) Id \\ f
  apply = Str Apply Id

type data TestTy = IntTy' | StringTy'
type IntTy = D.D IntTy'
type StringTy = D.D StringTy'
data Test a b where
  Show :: Test IntTy StringTy
  Read :: Test StringTy IntTy
  Succ :: Test IntTy IntTy
  Dup :: Test StringTy StringTy

shw :: (i :: FREE cs Test) ~> EMB IntTy %1 -> i ~> EMB StringTy
shw = Emb Show

read :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB IntTy
read = Emb Read

succ :: (i :: FREE cs Test) ~> EMB IntTy %1 -> i ~> EMB IntTy
succ = Emb Succ

dup :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
dup = Emb Dup

test :: (i :: FREE cs Test) ~> EMB StringTy %1 -> i ~> EMB StringTy
test x = dup (shw (succ (read x)))

test2
  :: (HasBinaryProducts (FREE cs Test)) => (i :: FREE cs Test) ~> EMB StringTy -> i ~> (EMB StringTy *! EMB StringTy)
test2 x = x &&& test x

type Interp :: D.DISCRETE TestTy +-> Type
data Interp a b where
  Interp :: (Ob b) => a ~> Interp % b -> Interp a b
instance Profunctor Interp where
  dimap = dimapRep
  r \\ Interp f = r \\ f
instance Representable Interp where
  type Interp % IntTy = P.Int
  type Interp % StringTy = P.String
  index (Interp f) = f
  tabulate f = Interp f
  repMap D.Refl = id

-- >>> testFold "123"
-- ("123","124124")
testFold :: P.String -> (P.String, P.String)
testFold = fold @'[HasBinaryProducts] @Interp interp (test2 Id)
  where
    interp :: Test x y -> Interp % x ~> Interp % y
    interp Show = P.show
    interp Read = P.read
    interp Succ = P.succ
    interp Dup = (\s -> s ++ s)
