{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Object.BinaryProduct where

import Data.Kind (Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..), Fst, Snd)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, PRO, Profunctor (..), Promonad (..), UN, src, type (+->), Category)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Product (prod, (:*:) (..))
import Proarrow.Object.Initial (HasInitialObject (..))

infixl 5 &&
infixl 5 &&&
infixl 5 ***

class (CategoryOf k) => HasBinaryProducts k where
  type (a :: k) && (b :: k) :: k
  fst :: (Ob (a :: k), Ob b) => (a && b) ~> a
  fst @a @b = fst' (obj @a) (obj @b)
  fst' :: (a :: k) ~> a' -> Obj b -> a && b ~> a'
  fst' @a @_ @b a b = a . fst @k @a @b \\ a \\ b
  snd' :: Obj (a :: k) -> b ~> b' -> a && b ~> b'
  snd' @a @b a b = b . snd @k @a @b \\ a \\ b
  snd :: (Ob (a :: k), Ob b) => (a && b) ~> b
  snd @a @b = snd' (obj @a) (obj @b)
  (&&&) :: (a :: k) ~> x -> a ~> y -> a ~> x && y
  (***) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a && b ~> x && y
  l *** r = (l . fst @k @a @b) &&& (r . snd @k @a @b) \\ l \\ r

first :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (a && c) ~> (b && c)
first f = f *** obj @c

second :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (c && a) ~> (c && b)
second f = obj @c *** f

diag :: forall {k} (a :: k). (HasBinaryProducts k, Ob a) => a ~> a && a
diag = id &&& id

type HasProducts k = (HasTerminalObject k, HasBinaryProducts k)

class (a ** b ~ a && b) => TensorIsProduct a b
instance (a ** b ~ a && b) => TensorIsProduct a b
class (HasProducts k, Monoidal k, (Unit :: k) ~ TerminalObject, forall (a :: k) (b :: k). TensorIsProduct a b) => Cartesian k
instance (HasProducts k, Monoidal k, (Unit :: k) ~ TerminalObject, forall (a :: k) (b :: k). TensorIsProduct a b) => Cartesian k

instance HasBinaryProducts Type where
  type a && b = (a, b)
  fst = P.fst
  snd = P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts () where
  type '() && '() = '()
  fst = U.Unit
  snd = U.Unit
  U.Unit &&& U.Unit = U.Unit

instance (HasBinaryProducts j, HasBinaryProducts k) => HasBinaryProducts (j, k) where
  type a && b = '(Fst a && Fst b, Snd a && Snd b)
  fst @'(a1, a2) @'(b1, b2) = fst @_ @a1 @b1 :**: fst @_ @a2 @b2
  snd @a @b = snd @_ @(Fst a) @(Fst b) :**: snd @_ @(Snd a) @(Snd b)
  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)

instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (PRO j k) where
  type p && q = p :*: q
  fst' (Prof n) Prof{} = Prof (n . fstP)
  snd' Prof{} (Prof n) = Prof (n . sndP)
  Prof l &&& Prof r = Prof (prod l r)

leftUnitorProd :: (HasProducts k) => (a :: k) ~> b -> TerminalObject && a ~> b
leftUnitorProd f = f . snd' (obj @TerminalObject) (src f)

leftUnitorProdInv :: (HasProducts k) => (a :: k) ~> b -> a ~> TerminalObject && b
leftUnitorProdInv f = terminate' (src f) &&& f

rightUnitorProd :: (HasProducts k) => (a :: k) ~> b -> a && TerminalObject ~> b
rightUnitorProd f = f . fst' (src f) (obj @TerminalObject)

rightUnitorProdInv :: (HasProducts k) => (a :: k) ~> b -> a ~> b && TerminalObject
rightUnitorProdInv f = f &&& terminate' (src f)

associatorProd :: (HasProducts k) => Obj (a :: k) -> Obj b -> Obj c -> (a && b) && c ~> a && (b && c)
associatorProd a b c = (fst' a b . fst' (a *** b) c) &&& (snd' a b *** c) \\ (a *** b)

associatorProdInv :: (HasProducts k) => Obj (a :: k) -> Obj b -> Obj c -> a && (b && c) ~> (a && b) && c
associatorProdInv a b c = (a *** fst' b c) &&& (snd' b c . snd' a (b *** c)) \\ (a *** b)

swapProd :: (HasBinaryProducts k) => (a :: k) ~> a' -> b ~> b' -> (a && b) ~> (b' && a')
swapProd a b = snd' (src a) b &&& fst' a (src b)

newtype PROD k = PR k
type instance UN PR (PR k) = k

type Prod :: j +-> k -> PROD j +-> PROD k
data Prod p (a :: PROD k) b where
  Prod :: {unProd :: p a b} -> Prod p (PR a) (PR b)

instance Profunctor p => Profunctor (Prod p) where
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
  fst @(PR a) @(PR b) = Prod (fst @_ @a @b)
  snd @(PR a) @(PR b) = Prod (snd @_ @a @b)
  Prod f &&& Prod g = Prod (f &&& g)
  Prod f *** Prod g = Prod (f *** g)
instance HasInitialObject k => HasInitialObject (PROD k) where
  type InitialObject = PR InitialObject
  initiate = Prod initiate

instance (HasProducts k, Category cat) => MonoidalProfunctor (Prod cat :: CAT (PROD k)) where
  par0 = id
  f `par` g = f *** g

instance (HasProducts k) => Monoidal (PROD k) where
  type Unit = TerminalObject
  type a ** b = a && b

  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance (HasProducts k) => SymMonoidal (PROD k) where
  swap' (Prod a) (Prod b) = Prod (swapProd a b)

instance MonoidalProfunctor (->) where
  par0 = id
  f `par` g = f *** g

instance Monoidal Type where
  type Unit = TerminalObject
  type a ** b = a && b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal Type where
  swap' = swapProd

instance MonoidalProfunctor U.Unit where
  par0 = id
  f `par` g = f *** g

instance Monoidal () where
  type Unit = TerminalObject
  type a ** b = a && b
  leftUnitor = leftUnitorProd
  leftUnitorInv = leftUnitorProdInv
  rightUnitor = rightUnitorProd
  rightUnitorInv = rightUnitorProdInv
  associator = associatorProd
  associatorInv = associatorProdInv

instance SymMonoidal () where
  swap' = swapProd
