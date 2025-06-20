{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Instance.Free where

import Data.Kind (Constraint)
import Data.Typeable (Typeable, eqT, (:~:) (..))
import Prelude (Bool (..), Eq (..), Maybe (..), (&&))
import Prelude qualified as P

import Proarrow.Category.Instance.Constraint (type (:=>))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..))
import Proarrow.Category.Monoidal qualified as M
import Proarrow.Core (Any, CAT, CategoryOf (..), Kind, Profunctor (..), Promonad (..), UN, dimapDefault, (:~>))
import Proarrow.Object.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Object.Exponential (Closed (..), eval)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Initial (InitialProfunctor)

newtype FREE (str :: Constraint) (p :: CAT k) = EMB k
type instance UN EMB (EMB a) = a

type Free :: CAT (FREE c p)
data Free a b where
  Id :: (Ob a) => Free a a
  Emb :: (Ob a, Ob b, Typeable a, Typeable b) => p a b -> Free (i :: FREE c p) (EMB a) -> Free i (EMB b)
  Str
    :: forall {k} {c} {p :: CAT k} (str :: CAT (FREE c p)) a b i
     . (c :=> HasStructure str k, Structure str, Ob a, Ob b)
    => str a b
    -> Free i a
    -> Free i b

class (forall x y. Eq (p x y)) => Eq2 p
instance (forall x y. Eq (p x y)) => Eq2 p

class (Typeable p, Typeable c, Typeable k) => Ok c p k
instance (Typeable p, Typeable c, Typeable k) => Ok c p k

class (Ok c p k, Eq2 p) => WithEq (a :: FREE c (p :: CAT k))
instance (Ok c p k, Eq2 p) => WithEq (a :: FREE c (p :: CAT k))

instance (WithEq a) => Eq (Free a b) where
  Id == Id = True
  Emb @al p1 g1 == Emb @ar p2 g2 = case eqT @al @ar of Just Refl -> p1 == p2 && g1 == g2; Nothing -> False
  Str @strl @al s1 g1 == Str @strr @a2 s2 g2 = case (eqT @strl @strr, eqT @al @a2) of
    (Just Refl, Just Refl) -> s1 == s2 && g1 == g2
    _ -> False
  _ == _ = False

type IsFreeOb :: forall {k} {c :: Constraint} {p :: CAT k}. FREE c p -> Constraint
class IsFreeOb (a :: FREE c (p :: CAT k)) where
  type Lower (a :: FREE c p) :: k
  withLowerOb :: ((Ob (Lower (a :: FREE c p))) => r) -> r
instance (Ob a, Typeable a) => IsFreeOb (EMB a) where
  type Lower (EMB a) = a
  withLowerOb r = r

class ((Ok c p k, Eq2 p) => Eq2 str, (Ok c p k) => Typeable str) => CanEq (str :: CAT (FREE c (p :: CAT k)))
instance ((Ok c p k, Eq2 p) => Eq2 str, (Ok c p k) => Typeable str) => CanEq (str :: CAT (FREE c (p :: CAT k)))

class (CanEq str) => Structure (str :: CAT (FREE c (p :: CAT k))) where
  type HasStructure str :: Kind -> Constraint
  foldStructure
    :: forall (a :: FREE c p) (b :: FREE c p)
     . (HasStructure str k, CategoryOf k)
    => (forall (x :: FREE c p) y. x ~> y -> Lower x ~> Lower y)
    -> str a b
    -> Lower a ~> Lower b

fold
  :: forall {k} {c :: Constraint} {p :: CAT k} (a :: FREE c p) (b :: FREE c p)
   . (CategoryOf k, c)
  => (p :~> (~>)) -> a ~> b -> Lower a ~> Lower b
fold pn = go
  where
    go :: forall (x :: FREE c p) y. x ~> y -> Lower x ~> Lower y
    go Id = withLowerOb @x id
    go (Emb p g) = pn p . go g
    go (Str s g) = foldStructure go s . go g

retract :: (CategoryOf k, c) => (a :: FREE c (InitialProfunctor :: CAT k)) ~> b -> Lower a ~> Lower b
retract = fold (\case {})

instance (Ok c p k) => CategoryOf (FREE c (p :: CAT k)) where
  type (~>) = Free
  type Ob a = (IsFreeOb a, Typeable a)

instance (Ok c p k) => Promonad (Free :: CAT (FREE c (p :: CAT k))) where
  id = Id
  Id . g = g
  f . Id = f
  Emb p f . g = Emb p (f . g)
  Str s f . g = Str s (f . g)

instance (Ok c p k) => Profunctor (Free :: CAT (FREE c (p :: CAT k))) where
  dimap = dimapDefault
  r \\ Id = r
  r \\ Emb _ f = r \\ f
  r \\ Str _ f = r \\ f

type Plain :: CAT (FREE c p)
data Plain a b
instance Eq (Plain a b) where
  (==) = \case {}
instance Structure (Plain :: CAT (FREE c (p :: CAT k))) where
  type HasStructure Plain = Any
  foldStructure _ = \case {}

data family TermF :: k
instance (HasTerminalObject k) => IsFreeOb (TermF :: FREE c (p :: CAT k)) where
  type Lower TermF = TerminalObject
  withLowerOb r = r
type Terminal :: CAT (FREE c p)
data Terminal a b where
  Terminal :: (Ob a) => Terminal a TermF
deriving instance Eq (Terminal a b)
instance Structure Terminal where
  type HasStructure Terminal = HasTerminalObject
  foldStructure _ (Terminal @a) = withLowerOb @a (terminate)
instance (HasTerminalObject k, Ok c p k) => HasTerminalObject (FREE c (p :: CAT k)) where
  type TerminalObject = TermF
  terminate = Str Terminal Id

data family InitF :: k
instance (HasInitialObject k) => IsFreeOb (InitF :: FREE c (p :: CAT k)) where
  type Lower InitF = InitialObject
  withLowerOb r = r
type Initial :: CAT (FREE c p)
data Initial a b where
  Initial :: (Ob b) => Initial InitF b
deriving instance Eq (Initial a b)
instance (Ok c p k) => Structure (Initial :: CAT (FREE c (p :: CAT k))) where
  type HasStructure Initial = HasInitialObject
  foldStructure _ (Initial @b) = withLowerOb @b initiate
instance (HasInitialObject k, Ok c p k) => HasInitialObject (FREE c (p :: CAT k)) where
  type InitialObject = InitF
  initiate = Str Initial Id

data family (*!) (a :: k) (b :: k) :: k
instance (HasBinaryProducts k, Ob (a :: FREE c (p :: CAT k)), Ob b) => IsFreeOb (a *! b) where
  type Lower (a *! b) = Lower a && Lower b
  withLowerOb r = withLowerOb @a (withLowerOb @b (withObProd @_ @(Lower a) @(Lower b) r))
type Product :: CAT (FREE c p)
data Product i o where
  Fst :: (Ob a, Ob b) => Product (a *! b) a
  Snd :: (Ob a, Ob b) => Product (a *! b) b
  Prd :: i ~> a -> i ~> b -> Product i (a *! b)
deriving instance (WithEq a) => Eq (Product a b)
instance Structure (Product :: CAT (FREE c (p :: CAT k))) where
  type HasStructure Product = HasBinaryProducts
  foldStructure _ (Fst @a @b) = withLowerOb @a (withLowerOb @b (fst @_ @(Lower a) @(Lower b)))
  foldStructure _ (Snd @a @b) = withLowerOb @a (withLowerOb @b (snd @_ @(Lower a) @(Lower b)))
  foldStructure go (Prd f g) = go f &&& go g
instance (HasBinaryProducts k, Ok c p k) => HasBinaryProducts (FREE c (p :: CAT k)) where
  type a && b = a *! b
  withObProd r = r
  fst = Str Fst Id
  snd = Str Snd Id
  f &&& g = Str (Prd f g) Id \\ f \\ g

data family (+) (a :: k) (b :: k) :: k
instance (HasBinaryCoproducts k, Ob (a :: FREE c (p :: CAT k)), Ob b) => IsFreeOb (a + b) where
  type Lower (a + b) = Lower a || Lower b
  withLowerOb r = withLowerOb @a (withLowerOb @b (withObCoprod @_ @(Lower a) @(Lower b) r))
type Coproduct :: CAT (FREE c p)
data Coproduct i o where
  Lft :: (Ob a, Ob b) => Coproduct a (a + b)
  Rgt :: (Ob a, Ob b) => Coproduct b (a + b)
  Sum :: a ~> o -> b ~> o -> Coproduct (a + b) o
deriving instance (WithEq a) => Eq (Coproduct a b)
instance Structure (Coproduct :: CAT (FREE c (p :: CAT k))) where
  type HasStructure Coproduct = HasBinaryCoproducts
  foldStructure _ (Lft @a @b) = withLowerOb @a (withLowerOb @b (lft @_ @(Lower a) @(Lower b)))
  foldStructure _ (Rgt @a @b) = withLowerOb @a (withLowerOb @b (rgt @_ @(Lower a) @(Lower b)))
  foldStructure go (Sum g h) = (go g ||| go h)
instance (HasBinaryCoproducts k, Ok c p k) => HasBinaryCoproducts (FREE c (p :: CAT k)) where
  type a || b = a + b
  withObCoprod r = r
  lft = Str Lft Id
  rgt = Str Rgt Id
  f ||| g = Str (Sum f g) Id \\ f \\ g

data family UnitF :: k
instance (Monoidal k) => IsFreeOb (UnitF :: FREE c (p :: CAT k)) where
  type Lower UnitF = Unit
  withLowerOb r = r
data family (**!) (a :: k) (b :: k) :: k
instance (Monoidal k, Ob (a :: FREE c (p :: CAT k)), Ob b) => IsFreeOb (a **! b) where
  type Lower (a **! b) = Lower a ** Lower b
  withLowerOb r = withLowerOb @a (withLowerOb @b (withOb2 @_ @(Lower a) @(Lower b) r))
data Tensor i o where
  Par0 :: Tensor UnitF UnitF
  Par :: a ~> b -> c ~> d -> Tensor (a **! c) (b **! d)
  LeftUnitor :: (Ob a) => Tensor (UnitF **! a) a
  LeftUnitorInv :: (Ob a) => Tensor a (UnitF **! a)
  RightUnitor :: (Ob a) => Tensor (a **! UnitF) a
  RightUnitorInv :: (Ob a) => Tensor a (a **! UnitF)
  Associator :: (Ob a, Ob b, Ob c) => Tensor ((a **! b) **! c) (a **! (b **! c))
  AssociatorInv :: (Ob a, Ob b, Ob c) => Tensor (a **! (b **! c)) ((a **! b) **! c)
deriving instance (WithEq a) => Eq (Tensor a b)
instance Structure (Tensor :: CAT (FREE c (p :: CAT k))) where
  type HasStructure Tensor = Monoidal
  foldStructure _ Par0 = par0
  foldStructure go (Par f g) = go f `par` go g
  foldStructure _ (LeftUnitor @a) = withLowerOb @a leftUnitor
  foldStructure _ (LeftUnitorInv @a) = withLowerOb @a leftUnitorInv
  foldStructure _ (RightUnitor @a) = withLowerOb @a rightUnitor
  foldStructure _ (RightUnitorInv @a) = withLowerOb @a rightUnitorInv
  foldStructure _ (Associator @a @b @c') = withLowerOb @a (withLowerOb @b (withLowerOb @c' (associator @_ @(Lower a) @(Lower b) @(Lower c'))))
  foldStructure _ (AssociatorInv @a @b @c') = withLowerOb @a (withLowerOb @b (withLowerOb @c' (associatorInv @_ @(Lower a) @(Lower b) @(Lower c'))))
instance (Monoidal k, Ok c p k) => MonoidalProfunctor (Free :: CAT (FREE c (p :: CAT k))) where
  par0 = Str Par0 Id
  f `par` g = Str (Par f g) Id \\ f \\ g
instance (Monoidal k, Ok c p k) => Monoidal (FREE c (p :: CAT k)) where
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
instance (Closed k, Ob (a :: FREE c (p :: CAT k)), Ob b) => IsFreeOb (a --> b) where
  type Lower (a --> b) = Lower a ~~> Lower b
  withLowerOb r = withLowerOb @a (withLowerOb @b (withObExp @_ @(Lower a) @(Lower b) r))
type Exponential :: CAT (FREE c p)
data Exponential i o where
  Apply :: (Ob a, Ob b) => Exponential ((a --> b) **! a) b
  Curry :: forall a i b. (Ob a, Ob i) => (i **! a) ~> b -> Exponential i (a --> b)
deriving instance (WithEq i, WithEq o) => Eq (Exponential i o)
instance Structure (Exponential :: CAT (FREE c (p :: CAT k))) where
  type HasStructure Exponential = Closed
  foldStructure _ (Apply @a @b) = withLowerOb @a (withLowerOb @b (eval @(Lower a) @(Lower b)))
  foldStructure go (Curry @a @i f) = withLowerOb @a (withLowerOb @i (curry @_ @(Lower i) @(Lower a) (go f)))
instance (Closed k, Ok c p k) => Closed (FREE c (p :: CAT k)) where
  type a ~~> b = a --> b
  withObExp r = r
  curry f = Str (Curry f) Id \\ f
  uncurry f = Str Apply (M.first f)

data Test a b where
  Show :: Test P.Int P.String
  Read :: Test P.String P.Int
  Succ :: Test P.Int P.Int
  Dup :: Test P.String P.String

show :: (i :: FREE () Test) ~> EMB P.Int -> i ~> EMB P.String
show = Emb Show

read :: (i :: FREE () Test) ~> EMB P.String -> i ~> EMB P.Int
read = Emb Read

succ :: (i :: FREE () Test) ~> EMB P.Int -> i ~> EMB P.Int
succ = Emb Succ

dup :: (i :: FREE () Test) ~> EMB P.String -> i ~> EMB P.String
dup = Emb Dup

test :: (i :: FREE () Test) ~> EMB P.String -> i ~> EMB P.String
test x = dup (show (succ (read x)))

test2 :: (i :: FREE () Test) ~> EMB P.String -> i ~> (EMB P.String *! EMB P.String)
test2 x = x &&& test x

-- >>> testFold "123"
-- ("123","124124")
testFold :: P.String -> (P.String, P.String)
testFold = fold interp (test2 Id)
  where
    interp :: Test :~> (->)
    interp Show = P.show
    interp Read = P.read
    interp Succ = P.succ
    interp Dup = \s -> s P.++ s
