{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Object.BinaryProduct where

import Data.Kind (Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, PRO, Profunctor (..), Promonad (..), UN, dimapDefault, src)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Product (prod, (:*:) (..))

infixl 5 &&
infixl 5 &&&
infixl 5 ***

class (CategoryOf k) => HasBinaryProducts k where
  type (a :: k) && (b :: k) :: k
  fst' :: (a :: k) ~> a' -> Obj b -> a && b ~> a'
  snd' :: Obj (a :: k) -> b ~> b' -> a && b ~> b'
  (&&&) :: (a :: k) ~> x -> a ~> y -> a ~> x && y
  (***) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a && b ~> x && y
  l *** r = (l . fst @a @b) &&& (r . snd @a @b) \\ l \\ r

fst :: forall {k} (a :: k) (b :: k). (HasBinaryProducts k, Ob a, Ob b) => (a && b) ~> a
fst = fst' (obj @a) (obj @b)

snd :: forall {k} (a :: k) (b :: k). (HasBinaryProducts k, Ob a, Ob b) => (a && b) ~> b
snd = snd' (obj @a) (obj @b)

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
  fst' f _ = f . P.fst
  snd' _ f = f . P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts () where
  type '() && '() = '()
  fst' U.Unit U.Unit = U.Unit
  snd' U.Unit U.Unit = U.Unit
  U.Unit &&& U.Unit = U.Unit

instance (HasBinaryProducts j, HasBinaryProducts k) => HasBinaryProducts (j, k) where
  type '(a1, a2) && '(b1, b2) = '(a1 && b1, a2 && b2)
  fst' (a1 :**: a2) (b1 :**: b2) = fst' a1 b1 :**: fst' a2 b2
  snd' (a1 :**: a2) (b1 :**: b2) = snd' a1 b1 :**: snd' a2 b2
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

type Prod :: CAT (PROD k)
data Prod (a :: PROD k) b where
  Prod :: {unProd :: a ~> b} -> Prod (PR a) (PR b)

instance (CategoryOf k) => Profunctor (Prod :: CAT (PROD k)) where
  dimap = dimapDefault
  r \\ Prod f = r \\ f
instance (CategoryOf k) => Promonad (Prod :: CAT (PROD k)) where
  id = Prod id
  Prod f . Prod g = Prod (f . g)
instance (CategoryOf k) => CategoryOf (PROD k) where
  type (~>) = Prod
  type Ob a = (Is PR a, Ob (UN PR a))

instance (HasTerminalObject k) => HasTerminalObject (PROD k) where
  type TerminalObject = PR TerminalObject
  terminate' (Prod a) = Prod (terminate' a)
instance (HasBinaryProducts k) => HasBinaryProducts (PROD k) where
  type a && b = PR (UN PR a && UN PR b)
  fst' (Prod a) (Prod b) = Prod (fst' a b)
  snd' (Prod a) (Prod b) = Prod (snd' a b)
  Prod f &&& Prod g = Prod (f &&& g)
  Prod f *** Prod g = Prod (f *** g)

instance (HasProducts k) => MonoidalProfunctor (Prod :: CAT (PROD k)) where
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
