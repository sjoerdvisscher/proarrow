{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Category.Instance.Free where

import Data.Kind (Constraint, Type)
import Data.Typeable (Typeable, eqT, (:~:) (..))
import GHC.Exts qualified as GHC
import Prelude (Bool (..), Eq (..), Maybe (..), and, (&&), (<$>))
import Prelude qualified as P

import Proarrow.Category.Instance.Discrete qualified as D
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Core
  ( CAT
  , Category
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

newtype FREE (cs :: [Kind -> Constraint]) (p :: CAT j) (k :: Kind) = EMB j
type instance UN EMB (EMB a) = a

type family All (cs :: [Kind -> Constraint]) (k :: Kind) :: Constraint where
  All '[] k = ()
  All (c ': cs) k = (c k, All cs k)

class cs `Includes` (c :: Kind -> Constraint)
instance {-# OVERLAPPABLE #-} (cs `Includes` c) => (d ': cs) `Includes` c
instance (c ': cs) `Includes` c

type Free :: CAT (FREE cs p k)
data Free a b where
  Id :: (Ob a) => Free a a
  Emb :: (Ob a, Ob b, Typeable a, Typeable b) => p a b %1 -> Free (i :: FREE cs p k) (EMB a) %1 -> Free i (EMB b)
  Str
    :: forall {j} {k} {cs} {p :: CAT j} (c :: Kind -> Constraint) (a :: FREE cs p k) b i
     . ((All cs k) => c k, cs `Includes` c, HasStructure k cs p c, Ob a, Ob b)
    => Struct c a b %1 -> Free i a %1 -> Free i b

emb :: (Ob a, Ob b, Typeable a, Typeable b, Ok cs p k) => p a b %1 -> Free (EMB a :: FREE cs p k) (EMB b)
emb p = Emb p Id

class (forall x y. Eq (p x y)) => Eq2 p
instance (forall x y. Eq (p x y)) => Eq2 p

class (forall x y. P.Show (p x y)) => Show2 p
instance (forall x y. P.Show (p x y)) => Show2 p

class (Typeable p, Typeable c, Typeable k, Typeable j) => Ok c (p :: CAT j) k
instance (Typeable p, Typeable c, Typeable k, Typeable j) => Ok c (p :: CAT j) k

class (Ok c p k, Eq2 p) => WithEq (a :: FREE c (p :: CAT j) k)
instance (Ok c p k, Eq2 p) => WithEq (a :: FREE c (p :: CAT j) k)

instance (WithEq a) => Eq (Free a b) where
  Id == Id = True
  Emb @al p1 g1 == Emb @ar p2 g2 = case eqT @al @ar of Just Refl -> p1 == p2 && g1 == g2; Nothing -> False
  Str @strl @a1 s1 g1 == Str @strr @a2 s2 g2 = case (eqT @strl @strr, eqT @a1 @a2) of
    (Just Refl, Just Refl) -> s1 == s2 && g1 == g2
    _ -> False
  _ == _ = False

type IsFreeOb :: forall {j} {cs :: [Kind -> Constraint]} {p :: CAT j} {k :: Kind}. FREE cs p k -> Constraint
class IsFreeOb (a :: FREE cs (p :: CAT j) k) where
  type Lower (f :: j +-> k) (a :: FREE cs p k) :: k
  withLowerOb :: (Representable f) => ((Ob (Lower f (a :: FREE cs p k))) => r) -> r
instance (Ob a, Typeable a) => IsFreeOb (EMB a) where
  type Lower f (EMB a) = f % a
  withLowerOb @f r = withRepOb @f @a r

class ((Ok c p k, Eq2 p) => Eq2 str, (Ok c p k) => Typeable str) => CanEq (str :: CAT (FREE c p k))
instance ((Ok c p k, Eq2 p) => Eq2 str, (Ok c p k) => Typeable str) => CanEq (str :: CAT (FREE c p k))

class (Typeable c, CanEq (Struct c :: CAT (FREE cs p k))) => HasStructure k cs (p :: CAT j) (c :: Kind -> Constraint) where
  data Struct c :: CAT (FREE cs p k)
  foldStructure
    :: forall (f :: j +-> k) (a :: FREE cs p k) (b :: FREE cs p k)
     . (c k, Representable f)
    => (forall (x :: FREE cs p k) y. x ~> y -> Lower f x ~> Lower f y)
    -> Struct c a b
    -> Lower f a ~> Lower f b

fold
  :: forall {j} {k} {p :: CAT j} (cs :: [Kind -> Constraint]) (f :: j +-> k) (a :: FREE cs p k) (b :: FREE cs p k)
   . (All cs k, Representable f)
  => (forall x y. p x y -> f (f % x) y)
  -> a ~> b
  -> Lower f a ~> Lower f b
fold pn = go
  where
    go :: forall (x :: FREE cs p k) y. x ~> y -> Lower f x ~> Lower f y
    go Id = withLowerOb @x @f id
    go (Emb p g) = index (pn p) . go g
    go (Str s g) = foldStructure @_ @_ @_ @_ @_ @f go s . go g

retract
  :: forall {k} cs f a b. (All cs k, Representable f) => (a :: FREE cs InitialProfunctor k) ~> b -> Lower f a ~> Lower f b
retract = fold @cs @f (\case {})

type Req (c :: Type -> Constraint) (lut :: [(GHC.Symbol, k)]) (a :: FREE cs p k) (b :: FREE cs p k)
  =() :: Constraint --( (Lower (Lookup lut) a) (Lower (Lookup lut) b), Show (Lower (Lookup lut) a), Show (Lower (Lookup lut) b))
infix 0 :=:
type AssertEqs :: (Kind -> Constraint) -> Kind -> Type
data AssertEqs c k  where
  NoLaws :: AssertEqs c k
  (:>>:) :: AssertEqs c k -> AssertEqs c k -> AssertEqs c k
  (:=:) :: forall {k} {c} (a :: FREE '[c] (Var c) k) (b :: FREE '[c] (Var c) k). (forall r lut. ((Req Eq lut a b, Req P.Show lut a b) => Free a b -> Free a b -> r) -> r) -> AssertEqs c k

(>>) :: AssertEqs c k -> AssertEqs c k -> AssertEqs c k
(>>) = (:>>:)

class Laws (c :: Kind -> Constraint) where
  data Var c (a :: GHC.Symbol) (b :: GHC.Symbol)
  laws :: (c k, Typeable k) => AssertEqs c k

type family AssocLookup (lut :: [(GHC.Symbol, k)]) (a :: GHC.Symbol) :: k where
  AssocLookup '[] a = GHC.Any
  AssocLookup ('(s, k) ': lut) s = k
  AssocLookup ('(s, k) ': lut) a = AssocLookup lut a

type family AllOb (lut :: [(GHC.Symbol, k)]) :: Constraint where
  AllOb '[] = ()
  AllOb ('(s, k) ': lut) = (Ob k, AllOb lut)

type Lookup :: [(GHC.Symbol, k)] -> GHC.Symbol +-> k
data Lookup lut a b where
  Lookup :: forall lut b a. (Ob b) => a ~> Lookup lut % b -> Lookup lut a b
instance (CategoryOf k, AllOb lut) => Profunctor (Lookup lut :: GHC.Symbol +-> k) where
  dimap = dimapRep
  r \\ Lookup f = r \\ f
instance (CategoryOf k, AllOb lut) => Representable (Lookup lut :: GHC.Symbol +-> k) where
  type Lookup lut % a = AssocLookup lut a
  index (Lookup f) = f
  tabulate f = Lookup f
  -- We can't prove Ob (AssocLookup lut a), since `a` might not occur in `lut`, so we can't implement repMap.
  -- But Lookup is only for use with props, and props doesn't use repMap.
  -- Also the `pn` argument to props proves that all the symbols used in Var are in lut.
  repMap = P.error "repMap should not be used with Lookup"

instance Profunctor ((:~:) :: CAT GHC.Symbol) where
  dimap = dimapDefault
  r \\ Refl = r
instance Promonad ((:~:) :: CAT GHC.Symbol) where
  id = Refl
  Refl . Refl = Refl
instance CategoryOf GHC.Symbol where
  type (~>) = (:~:)
  type Ob a = ()

-- props
--   :: forall {k} (lut :: [(GHC.Symbol, k)]) c (cat :: CAT k)
--    . (c k, Laws c, Ok c (Var c) k, Eq2 cat, Category cat, AllOb lut)
--   => (forall x y. Var c x y -> Lookup lut % x ~> Lookup lut % y) -> Bool
-- props pn = and ((\(l :=: r) -> let f g = fold @'[c] (Lookup @lut . pn) g \\ g in f l == f r) <$> laws @c @k)

instance Laws HasBinaryProducts where
  data Var HasBinaryProducts a b where
    F :: Var HasBinaryProducts "A" "B"
    G :: Var HasBinaryProducts "A" "C"
  laws = NoLaws
    -- let f = emb F; g = emb G
    -- fst . (f &&& g) :=: f
    -- snd . (f &&& g) :=: g

instance (Ok c p k) => CategoryOf (FREE c p k) where
  type (~>) = Free
  type Ob a = (IsFreeOb a, Typeable a)

instance (Ok c p k) => Promonad (Free :: CAT (FREE c p k)) where
  id = Id
  Id . g = g
  f . Id = f
  Emb p f . g = Emb p (f . g)
  Str s f . g = Str s (f . g)

instance (Ok c p k) => Profunctor (Free :: CAT (FREE c p k)) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Emb _ f = r \\ f
  r \\ Str _ f = r \\ f

data family TermF :: k
instance (HasTerminalObject k) => IsFreeOb (TermF :: FREE c p k) where
  type Lower f TermF = TerminalObject
  withLowerOb r = r
instance HasStructure k cs p HasTerminalObject where
  data Struct HasTerminalObject a b where
    Terminal :: (Ob a) => Struct HasTerminalObject a TermF
  foldStructure @f _ (Terminal @a) = withLowerOb @a @f (terminate)
deriving instance Eq (Struct HasTerminalObject a b)
instance (HasTerminalObject k, Ok cs p k, cs `Includes` HasTerminalObject) => HasTerminalObject (FREE cs p k) where
  type TerminalObject = TermF
  terminate = Str Terminal Id

data family InitF :: k
instance (HasInitialObject k) => IsFreeOb (InitF :: FREE c p k) where
  type Lower f InitF = InitialObject
  withLowerOb r = r
instance HasStructure k cs p HasInitialObject where
  data Struct HasInitialObject a b where
    Initial :: (Ob b) => Struct HasInitialObject InitF b
  foldStructure @f _ (Initial @b) = withLowerOb @b @f initiate
deriving instance Eq (Struct HasInitialObject a b)
instance (HasInitialObject k, Ok cs p k, cs `Includes` HasInitialObject) => HasInitialObject (FREE cs p k) where
  type InitialObject = InitF
  initiate = Str Initial Id

data family (*!) (a :: k) (b :: k) :: k
instance (HasBinaryProducts k, Ob (a :: FREE c p k), Ob b) => IsFreeOb (a *! b) where
  type Lower f (a *! b) = Lower f a && Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withObProd @_ @(Lower f a) @(Lower f b) r))
instance HasStructure k cs p HasBinaryProducts where
  data Struct HasBinaryProducts i o where
    Fst :: (Ob a, Ob b) => Struct HasBinaryProducts (a *! b) a
    Snd :: (Ob a, Ob b) => Struct HasBinaryProducts (a *! b) b
    Prd :: i ~> a -> i ~> b -> Struct HasBinaryProducts i (a *! b)
  foldStructure @f _ (Fst @a @b) = withLowerOb @a @f (withLowerOb @b @f (fst @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (Snd @a @b) = withLowerOb @a @f (withLowerOb @b @f (snd @_ @(Lower f a) @(Lower f b)))
  foldStructure go (Prd f g) = go f &&& go g
deriving instance (WithEq a) => Eq (Struct HasBinaryProducts a b)
instance (HasBinaryProducts k, Ok cs p k, cs `Includes` HasBinaryProducts) => HasBinaryProducts (FREE cs p k) where
  type a && b = a *! b
  withObProd r = r
  fst = Str Fst Id
  snd = Str Snd Id
  f &&& g = Str (Prd f g) Id \\ f \\ g

data family (+) (a :: k) (b :: k) :: k
instance (HasBinaryCoproducts k, Ob (a :: FREE c p k), Ob b) => IsFreeOb (a + b) where
  type Lower f (a + b) = Lower f a || Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withObCoprod @_ @(Lower f a) @(Lower f b) r))
instance HasStructure k cs p HasBinaryCoproducts where
  data Struct HasBinaryCoproducts i o where
    Lft :: (Ob a, Ob b) => Struct HasBinaryCoproducts a (a + b)
    Rgt :: (Ob a, Ob b) => Struct HasBinaryCoproducts b (a + b)
    Sum :: a ~> o -> b ~> o -> Struct HasBinaryCoproducts (a + b) o
  foldStructure @f _ (Lft @a @b) = withLowerOb @a @f (withLowerOb @b @f (lft @_ @(Lower f a) @(Lower f b)))
  foldStructure @f _ (Rgt @a @b) = withLowerOb @a @f (withLowerOb @b @f (rgt @_ @(Lower f a) @(Lower f b)))
  foldStructure go (Sum g h) = (go g ||| go h)
deriving instance (WithEq a) => Eq (Struct HasBinaryCoproducts a b)
instance (HasBinaryCoproducts k, Ok cs p k, cs `Includes` HasBinaryCoproducts) => HasBinaryCoproducts (FREE cs p k) where
  type a || b = a + b
  withObCoprod r = r
  lft = Str Lft Id
  rgt = Str Rgt Id
  f ||| g = Str (Sum f g) Id \\ f \\ g

data family UnitF :: k
instance (Monoidal k) => IsFreeOb (UnitF :: FREE cs p k) where
  type Lower f UnitF = Unit
  withLowerOb r = r
data family (**!) (a :: k) (b :: k) :: k
instance (Monoidal k, Ob (a :: FREE cs p k), Ob b) => IsFreeOb (a **! b) where
  type Lower f (a **! b) = Lower f a ** Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withOb2 @_ @(Lower f a) @(Lower f b) r))
instance HasStructure k cs p Monoidal where
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
instance (Monoidal k, Ok cs p k, cs `Includes` Monoidal) => MonoidalProfunctor (Free :: CAT (FREE cs p k)) where
  par0 = Str Par0 Id
  f `par` g = Str (Par f g) Id \\ f \\ g
instance (Monoidal k, Ok cs p k, cs `Includes` Monoidal) => Monoidal (FREE cs p k) where
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
instance (Closed k, Ob (a :: FREE cs p k), Ob b) => IsFreeOb (a --> b) where
  type Lower f (a --> b) = Lower f a ~~> Lower f b
  withLowerOb @f r = withLowerOb @a @f (withLowerOb @b @f (withObExp @_ @(Lower f a) @(Lower f b) r))
instance HasStructure k cs p Closed where
  data Struct Closed a b where
    Apply :: (Ob a, Ob b) => Struct Closed ((a --> b) **! a) b
    Curry :: forall a b c. (Ob a, Ob b) => (a **! b) ~> c -> Struct Closed a (b --> c)
  foldStructure @f _ (Apply @a @b) = withLowerOb @a @f (withLowerOb @b @f (apply @_ @(Lower f a) @(Lower f b)))
  foldStructure @f go (Curry @a @b f) = withLowerOb @a @f (withLowerOb @b @f (curry @_ @(Lower f a) @(Lower f b) (go f)))
deriving instance (WithEq a) => Eq (Struct Closed a b)
instance (Closed k, Ok cs p k, cs `Includes` Closed, cs `Includes` Monoidal) => Closed (FREE cs p k) where
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

show :: (i :: FREE cs Test k) ~> EMB IntTy %1 -> i ~> EMB StringTy
show = Emb Show

read :: (i :: FREE cs Test k) ~> EMB StringTy %1 -> i ~> EMB IntTy
read = Emb Read

succ :: (i :: FREE cs Test k) ~> EMB IntTy %1 -> i ~> EMB IntTy
succ = Emb Succ

dup :: (i :: FREE cs Test k) ~> EMB StringTy %1 -> i ~> EMB StringTy
dup = Emb Dup

test :: (i :: FREE cs Test k) ~> EMB StringTy %1 -> i ~> EMB StringTy
test x = dup (show (succ (read x)))

test2
  :: (HasBinaryProducts (FREE cs Test k)) => (i :: FREE cs Test k) ~> EMB StringTy -> i ~> (EMB StringTy *! EMB StringTy)
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
testFold = fold @'[HasBinaryProducts] interp (test2 Id)
  where
    interp :: Test x y -> Interp (Interp % x) y
    interp Show = Interp P.show
    interp Read = Interp P.read
    interp Succ = Interp P.succ
    interp Dup = Interp (\s -> s P.++ s)
