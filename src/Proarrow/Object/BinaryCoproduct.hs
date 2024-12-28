{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
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

swapCoprod' :: (HasBinaryCoproducts k) => (a :: k) ~> a' -> b ~> b' -> (a || b) ~> (b' || a')
swapCoprod' a b = rgt' (tgt b) a ||| lft' b (tgt a)

swapCoprod :: (HasBinaryCoproducts k, Ob a, Ob b) => (a :: k) || b ~> b || a
swapCoprod @_ @a @b = swapCoprod' (obj @a) (obj @b)

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
  leftUnitor = Coprod (initiate ||| id)
  leftUnitorInv = Coprod (rgt @_ @InitialObject)
  rightUnitor = Coprod (id ||| initiate)
  rightUnitorInv = Coprod (lft @_ @_ @InitialObject)
  associator @(COPR a) @(COPR b) @(COPR c) = Coprod ((obj @a +++ lft @k @b @c) ||| (rgt @k @a @(b || c) . rgt @k @b @c) \\ (obj @b +++ obj @c))
  associatorInv @(COPR a) @(COPR b) @(COPR c) = Coprod ((lft @k @(a || b) @c . lft @k @a @b) ||| (rgt @k @a @b +++ obj @c) \\ (obj @a +++ obj @b))

instance (HasCoproducts k) => SymMonoidal (COPROD k) where
  swap' (Coprod a) (Coprod b) = Coprod (rgt' (tgt b) a ||| lft' b (tgt a))

instance Strong (Coprod (->)) (Coprod (->)) where
  act = par
instance MonoidalAction (COPROD Type) (COPROD Type) where
  type Act p x = p ** x
  unitor = leftUnitor
  unitorInv = leftUnitorInv
  multiplicator = associatorInv
  multiplicatorInv = associator

instance Strong (->) (Coprod (->)) where
  l `act` Coprod r = Coprod (l `par` r)
instance MonoidalAction Type (COPROD Type) where
  type Act (p :: Type) (COPR x :: COPROD Type) = COPR (p ** x)
  unitor = Coprod leftUnitor
  unitorInv = Coprod leftUnitorInv
  multiplicator = Coprod associatorInv
  multiplicatorInv = Coprod associator

instance Strong (Coprod (->)) (->) where
  f@Coprod{} `act` g = unCoprod (f `par` Coprod g)
instance MonoidalAction (COPROD Type) Type where
  type Act (p :: COPROD Type) (x :: Type) = UN COPR (p ** COPR x)
  unitor = unCoprod leftUnitor
  unitorInv = unCoprod leftUnitorInv
  multiplicator = unCoprod associatorInv
  multiplicatorInv = unCoprod associator

class (Act a b ~ (a || b)) => ActIsCoprod a b
instance (Act a b ~ (a || b)) => ActIsCoprod a b
class (Strong ((~>) :: CAT k) p, HasCoproducts k, forall (a :: k) (b :: k). ActIsCoprod a b) => StrongCoprod (p :: CAT k)
instance (Strong ((~>) :: CAT k) p, HasCoproducts k, forall (a :: k) (b :: k). ActIsCoprod a b) => StrongCoprod (p :: CAT k)

left' :: forall {k} (p :: CAT k) c a b. (StrongCoprod p, Ob c) => p a b -> p (a || c) (b || c)
left' p = dimap (swapCoprod @_ @a @c) (swapCoprod @_ @c @b) (right' @_ @c p) \\ p

right' :: forall {k} (p :: CAT k) c a b. (StrongCoprod p, Ob c) => p a b -> p (c || a) (c || b)
right' p = act @((~>) :: CAT k) (obj @c) p
