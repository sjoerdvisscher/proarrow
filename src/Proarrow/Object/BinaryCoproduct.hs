{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.BinaryCoproduct where

import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude (type (~))
import Prelude qualified as P

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, Category, CategoryOf (..), Is, PRO, Profunctor (..), Promonad (..), UN, type (+->))
import Proarrow.Object (Obj, obj, src, tgt)
import Proarrow.Object.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Coproduct (coproduct, (:+:) (..))
import Proarrow.Profunctor.Product ((:*:)(..))

infixl 4 ||
infixl 4 |||
infixl 4 +++

class (CategoryOf k) => HasBinaryCoproducts k where
  type (a :: k) || (b :: k) :: k
  lft' :: (a :: k) ~> a' -> Obj b -> a ~> (a' || b)
  rgt' :: Obj (a :: k) -> b ~> b' -> b ~> (a || b')
  (|||) :: (x :: k) ~> a -> y ~> a -> (x || y) ~> a
  (+++) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a || b ~> x || y
  l +++ r = (lft @x @y . l) ||| (rgt @x @y . r) \\ l \\ r

lft :: forall {k} (a :: k) (b :: k). (HasBinaryCoproducts k, Ob a, Ob b) => a ~> (a || b)
lft = lft' (obj @a) (obj @b)

rgt :: forall {k} (a :: k) (b :: k). (HasBinaryCoproducts k, Ob a, Ob b) => b ~> (a || b)
rgt = rgt' (obj @a) (obj @b)

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
  lft' f _ = P.Left . f
  rgt' _ f = P.Right . f
  (|||) = P.either

instance HasBinaryCoproducts () where
  type '() || '() = '()
  lft' U.Unit U.Unit = U.Unit
  rgt' U.Unit U.Unit = U.Unit
  U.Unit ||| U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (PRO j k) where
  type p || q = p :+: q
  lft' (Prof n) Prof{} = Prof (InjL . n)
  rgt' Prof{} (Prof n) = Prof (InjR . n)
  Prof l ||| Prof r = Prof (coproduct l r)

instance HasBinaryCoproducts k => HasBinaryCoproducts (PROD k) where
  type PR a || PR b = PR (a || b)
  lft' (Prod f) (Prod b) = Prod (lft' f b)
  rgt' (Prod a) (Prod f) = Prod (rgt' a f)
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
  leftUnitor (Coprod f) = Coprod (initiate' (tgt f) ||| f)
  leftUnitorInv (Coprod f) = Coprod (rgt' (obj @InitialObject) (tgt f) . f)
  rightUnitor (Coprod f) = Coprod (f ||| initiate' (tgt f))
  rightUnitorInv (Coprod f) = Coprod (lft' (tgt f) (obj @InitialObject) . f)
  associator (Coprod a) (Coprod b) (Coprod c) = Coprod ((a +++ lft' b c) ||| (rgt' a (b +++ c) . rgt' b c) \\ (a +++ b))
  associatorInv (Coprod a) (Coprod b) (Coprod c) = Coprod ((lft' (a +++ b) c . lft' a b) ||| (rgt' a b +++ c) \\ (a +++ b))

instance (HasCoproducts k) => SymMonoidal (COPROD k) where
  swap' (Coprod a) (Coprod b) = Coprod (rgt' (tgt b) a ||| lft' b (tgt a))

class (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p
instance (MonoidalProfunctor p, MonoidalProfunctor (Coprod p)) => DistributiveProfunctor p

class (Monoidal k, HasCoproducts k, DistributiveProfunctor ((~>) :: CAT k)) => Distributive k where
  distL' :: (a :: k) ~> a' -> b ~> b' -> c ~> c' -> (a ** (b || c)) ~> (a' ** b' || a' ** c')
  distR' :: (a :: k) ~> a' -> b ~> b' -> c ~> c' -> ((a || b) ** c) ~> (a' ** c' || b' ** c')
  default distR' :: (SymMonoidal k) => (a :: k) ~> a' -> b ~> b' -> c ~> c' -> ((a || b) ** c) ~> (a' ** c' || b' ** c')
  distR' fa fb fc = (swap' (tgt fc) (tgt fa) +++ swap' (tgt fc) (tgt fb))  . distL' fc fa fb . swap' (src fa +++ src fb) (src fc)
  distL0' :: Obj (a :: k) -> (a ** InitialObject) ~> InitialObject
  distR0' :: Obj (a :: k) -> (InitialObject ** a) ~> InitialObject

instance Distributive Type where
  distL' fa fb fc (a, e) = let a' = fa a in bimap ((a',) . fb) ((a',) . fc) e
  distR' fa fb fc (e, c) = let c' = fc c in bimap ((,c') . fa) ((,c') . fb) e
  distL0' _ = P.snd
  distR0' _ = P.fst

instance Distributive () where
  distL' U.Unit U.Unit U.Unit = U.Unit
  distR' U.Unit U.Unit U.Unit = U.Unit
  distL0' U.Unit = U.Unit
  distR0' U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => Distributive (PROD (PRO j k)) where
  distL' (Prod (Prof na)) (Prod (Prof nb)) (Prod (Prof nc)) = Prod (Prof \(a :*: bc) -> case bc of
      InjL b -> InjL (na a :*: nb b)
      InjR c -> InjR (na a :*: nc c)
    )
  distR' (Prod (Prof na)) (Prod (Prof nb)) (Prod (Prof nc)) = Prod (Prof \(ab :*: c) -> case ab of
      InjL a -> InjL (na a :*: nc c)
      InjR b -> InjR (nb b :*: nc c)
    )
  distL0' (Prod Prof{}) = Prod (Prof \(_ :*: i) -> case i of {})
  distR0' (Prod Prof{}) = Prod (Prof \(i :*: _) -> case i of {})