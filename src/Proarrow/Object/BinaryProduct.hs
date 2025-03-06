{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Object.BinaryProduct where

import Data.Kind (Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Product (Fst, Snd, (:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , TracedMonoidalProfunctor (..)
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), SelfAction, Strong (..))
import Proarrow.Core (CAT, Category, CategoryOf (..), Is, PRO, Profunctor (..), Promonad (..), UN, src, type (+->))
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Object.Terminal (HasTerminalObject (..), Semicartesian)
import Proarrow.Profunctor.Product (prod, (:*:) (..))

infixl 5 &&
infixl 5 &&&
infixl 5 ***

class (CategoryOf k) => HasBinaryProducts k where
  type (a :: k) && (b :: k) :: k
  withObProd :: (Ob (a :: k), Ob b) => ((Ob (a && b)) => r) -> r
  fst :: (Ob (a :: k), Ob b) => (a && b) ~> a
  snd :: (Ob (a :: k), Ob b) => (a && b) ~> b
  (&&&) :: (a :: k) ~> x -> a ~> y -> a ~> x && y
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

type HasProducts k = (HasTerminalObject k, HasBinaryProducts k)

class (a ** b ~ a && b) => TensorIsProduct a b
instance (a ** b ~ a && b) => TensorIsProduct a b
class (HasProducts k, SymMonoidal k, Semicartesian k, forall (a :: k) (b :: k). TensorIsProduct a b) => Cartesian k
instance (HasProducts k, SymMonoidal k, Semicartesian k, forall (a :: k) (b :: k). TensorIsProduct a b) => Cartesian k

instance HasBinaryProducts Type where
  type a && b = (a, b)
  withObProd r = r
  fst = P.fst
  snd = P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts () where
  type '() && '() = '()
  withObProd r = r
  fst = U.Unit
  snd = U.Unit
  U.Unit &&& U.Unit = U.Unit

instance (HasBinaryProducts j, HasBinaryProducts k) => HasBinaryProducts (j, k) where
  type a && b = '(Fst a && Fst b, Snd a && Snd b)
  withObProd @'(a1, a2) @'(b1, b2) r = withObProd @j @a1 @b1 (withObProd @k @a2 @b2 r)
  fst @'(a1, a2) @'(b1, b2) = fst @_ @a1 @b1 :**: fst @_ @a2 @b2
  snd @a @b = snd @_ @(Fst a) @(Fst b) :**: snd @_ @(Snd a) @(Snd b)
  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)

instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (PRO j k) where
  type p && q = p :*: q
  withObProd r = r
  fst = Prof fstP
  snd = Prof sndP
  Prof l &&& Prof r = Prof (prod l r)

leftUnitorProd :: forall {k} (a :: k). (HasProducts k, Ob a) => TerminalObject && a ~> a
leftUnitorProd = snd @k @TerminalObject

leftUnitorProdInv :: forall {k} (a :: k). (HasProducts k, Ob a) => a ~> TerminalObject && a
leftUnitorProdInv = terminate &&& id

rightUnitorProd :: forall {k} (a :: k). (HasProducts k, Ob a) => a && TerminalObject ~> a
rightUnitorProd = fst @k @_ @TerminalObject

rightUnitorProdInv :: forall {k} (a :: k). (HasProducts k, Ob a) => a ~> a && TerminalObject
rightUnitorProdInv = id &&& terminate

associatorProd :: forall {k} (a :: k) b c. (HasProducts k, Ob a, Ob b, Ob c) => (a && b) && c ~> a && (b && c)
associatorProd = (fst @k @a @b . fst @k @(a && b) @c) &&& (snd @k @a @b *** obj @c) \\ (obj @a *** obj @b)

associatorProdInv :: forall {k} (a :: k) b c. (HasProducts k, Ob a, Ob b, Ob c) => a && (b && c) ~> (a && b) && c
associatorProdInv = (obj @a *** fst @k @b @c) &&& (snd @k @b @c . snd @k @a @(b && c)) \\ (obj @b *** obj @c)

swapProd' :: (HasBinaryProducts k) => (a :: k) ~> a' -> b ~> b' -> (a && b) ~> (b' && a')
swapProd' a b = snd' (src a) b &&& fst' a (src b)

swapProd :: forall {k} (a :: k) b. (HasBinaryProducts k, Ob a, Ob b) => a && b ~> b && a
swapProd = swapProd' (obj @a) (obj @b)

newtype PROD k = PR k
type instance UN PR (PR k) = k

type Prod :: j +-> k -> PROD j +-> PROD k
data Prod p (a :: PROD k) b where
  Prod :: {unProd :: p a b} -> Prod p (PR a) (PR b)

instance (Profunctor p) => Profunctor (Prod p) where
  dimap (Prod l) (Prod r) (Prod p) = Prod (dimap l r p)
  r \\ Prod f = r \\ f
instance (Promonad p) => Promonad (Prod p) where
  id = Prod id
  Prod f . Prod g = Prod (f . g)
instance (CategoryOf k) => CategoryOf (PROD k) where
  type (~>) = Prod (~>)
  type Ob a = (Is PR a, Ob (UN PR a))

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

instance (HasProducts k, Category cat) => MonoidalProfunctor (Prod cat :: CAT (PROD k)) where
  par0 = id
  f `par` g = f *** g

instance (HasProducts k) => Monoidal (PROD k) where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 @(PR a) @(PR b) = withObProd @k @a @b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator @(PR a) @(PR b) @(PR c) = Prod (associatorProd @a @b @c)
  associatorInv @(PR a) @(PR b) @(PR c) = Prod (associatorProdInv @a @b @c)

instance (HasProducts k) => SymMonoidal (PROD k) where
  swap @(PR a) @(PR b) = Prod (swapProd @a @b)

instance MonoidalProfunctor (->) where
  par0 = id
  f `par` g = f *** g

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

instance Strong Type (->) where
  act = par
instance MonoidalAction Type Type where
  type Act p x = p ** x
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator = associatorInv
  multiplicatorInv = associator

instance TracedMonoidalProfunctor (->) where
  trace f x = let (y, u) = f (x, u) in y

instance MonoidalProfunctor U.Unit where
  par0 = id
  f `par` g = f *** g

instance Monoidal () where
  type Unit = TerminalObject
  type a ** b = a && b
  withOb2 r = r
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal () where
  swap = swapProd

instance Strong () U.Unit where
  act = par
instance MonoidalAction () () where
  type Act p x = p ** x
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator = associatorInv
  multiplicatorInv = associator

instance TracedMonoidalProfunctor U.Unit where
  trace U.Unit = U.Unit

class (Act a b ~ a && b) => ActIsProd a b
instance (Act a b ~ a && b) => ActIsProd a b
class (Act a (Act b c) ~ a && (b && c)) => ActIsProd3 a b c
instance (Act a (Act b c) ~ a && (b && c)) => ActIsProd3 a b c
class
  ( Cartesian k
  , SelfAction k
  , forall (a :: k) (b :: k). ActIsProd a b
  , forall (a :: k) (b :: k) (c :: k). ActIsProd3 a b c
  ) =>
  ProdAction k
instance
  ( Cartesian k
  , SelfAction k
  , forall (a :: k) (b :: k). ActIsProd a b
  , forall (a :: k) (b :: k) (c :: k). ActIsProd3 a b c
  )
  => ProdAction k
class (Strong k p, ProdAction k) => StrongProd (p :: CAT k)
instance (Strong k p, ProdAction k) => StrongProd (p :: CAT k)
