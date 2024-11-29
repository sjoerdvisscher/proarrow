{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, Category, CategoryOf (..), Is, PRO, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object (Obj, obj, tgt)
import Proarrow.Object.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Coproduct (coproduct, (:+:) (..))

infixl 4 ||
infixl 4 |||
infixl 4 +++

class (CategoryOf k) => HasBinaryCoproducts k where
  type (a :: k) || (b :: k) :: k
  lft :: (Ob (a :: k), Ob b) => a ~> (a || b)
  lft @a @b = lft' (obj @a) (obj @b)
  lft' :: (a :: k) ~> a' -> Obj b -> a ~> (a' || b)
  lft' @_ @a' @b a b = lft @k @a' @b . a \\ a \\ b
  rgt :: (Ob (a :: k), Ob b) => b ~> (a || b)
  rgt @a @b = rgt' (obj @a) (obj @b)
  rgt' :: Obj (a :: k) -> b ~> b' -> b ~> (a || b')
  rgt' @a @_ @b' a b = rgt @k @a @b' . b \\ a \\ b
  (|||) :: (x :: k) ~> a -> y ~> a -> (x || y) ~> a
  (+++) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a || b ~> x || y
  l +++ r = (lft @k @x @y . l) ||| (rgt @k @x @y . r) \\ l \\ r

left :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryCoproducts k, Ob c) => a ~> b -> (a || c) ~> (b || c)
left f = f +++ obj @c

right :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryCoproducts k, Ob c) => a ~> b -> (c || a) ~> (c || b)
right f = obj @c +++ f

codiag :: forall {k} (a :: k). (HasBinaryCoproducts k, Ob a) => (a || a) ~> a
codiag = id ||| id

type HasCoproducts k = (HasInitialObject k, HasBinaryCoproducts k)

class ((a ** b) ~ (a || b)) => TensorIsCoproduct a b
instance ((a ** b) ~ (a || b)) => TensorIsCoproduct a b
class
  (HasCoproducts k, Monoidal k, (Unit :: k) ~ InitialObject, forall (a :: k) (b :: k). TensorIsCoproduct a b) =>
  Cocartesian k
instance
  (HasCoproducts k, Monoidal k, (Unit :: k) ~ InitialObject, forall (a :: k) (b :: k). TensorIsCoproduct a b)
  => Cocartesian k

instance HasBinaryCoproducts Type where
  type a || b = P.Either a b
  lft = P.Left
  rgt = P.Right
  (|||) = P.either

instance HasBinaryCoproducts () where
  type '() || '() = '()
  lft = U.Unit
  rgt = U.Unit
  U.Unit ||| U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (PRO j k) where
  type p || q = p :+: q
  lft = Prof InjL
  rgt = Prof InjR
  Prof l ||| Prof r = Prof (coproduct l r)

instance (HasBinaryCoproducts k) => HasBinaryCoproducts (PROD k) where
  type PR a || PR b = PR (a || b)
  lft @(PR a) @(PR b) = Prod (lft @_ @a @b)
  rgt @(PR a) @(PR b) = Prod (rgt @_ @a @b)
  Prod l ||| Prod r = Prod (l ||| r)

newtype COPROD k = COPR k
type instance UN COPR (COPR k) = k

type Coprod :: j +-> k -> COPROD j +-> COPROD k
data Coprod p a b where
  Coprod :: {unCoprod :: p a b} -> Coprod p (COPR a) (COPR b)

instance (Profunctor p) => Profunctor (Coprod p) where
  dimap (Coprod l) (Coprod r) (Coprod p) = Coprod (dimap l r p)
  r \\ Coprod f = r \\ f
instance (Promonad p) => Promonad (Coprod p) where
  id = Coprod id
  Coprod f . Coprod g = Coprod (f . g)
instance (CategoryOf k) => CategoryOf (COPROD k) where
  type (~>) = Coprod (~>)
  type Ob a = (Is COPR a, Ob (UN COPR a))

instance (HasCoproducts k, Category cat) => MonoidalProfunctor (Coprod cat :: CAT (COPROD k)) where
  par0 = id
  Coprod f `par` Coprod g = Coprod (f +++ g)

instance (HasCoproducts k) => Monoidal (COPROD k) where
  type Unit = COPR InitialObject
  type a ** b = COPR (UN COPR a || UN COPR b)
  leftUnitor (Coprod f) = Coprod (initiate ||| f) \\ f
  leftUnitorInv (Coprod f) = Coprod (rgt @_ @InitialObject . f) \\ f
  rightUnitor (Coprod f) = Coprod (f ||| initiate) \\ f
  rightUnitorInv (Coprod f) = Coprod (lft @_ @_ @InitialObject . f) \\ f
  associator (Coprod a) (Coprod b) (Coprod c) = Coprod ((a +++ lft' b c) ||| (rgt' a (b +++ c) . rgt' b c) \\ (a +++ b))
  associatorInv (Coprod a) (Coprod b) (Coprod c) = Coprod ((lft' (a +++ b) c . lft' a b) ||| (rgt' a b +++ c) \\ (a +++ b))

instance (HasCoproducts k) => SymMonoidal (COPROD k) where
  swap' (Coprod a) (Coprod b) = Coprod (rgt' (tgt b) a ||| lft' b (tgt a))
