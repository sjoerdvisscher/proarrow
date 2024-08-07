{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, PRO, Profunctor (..), Promonad (..), UN, dimapDefault, tgt)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Initial (HasInitialObject (..))
import Proarrow.Profunctor.Coproduct (coproduct, (:+:) (..))

class (CategoryOf k) => HasBinaryCoproducts k where
  type (a :: k) || (b :: k) :: k
  lft' :: Obj (a :: k) -> Obj b -> a ~> (a || b)
  rgt' :: Obj (a :: k) -> Obj b -> b ~> (a || b)
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

instance HasBinaryCoproducts Type where
  type a || b = P.Either a b
  lft' _ _ = P.Left
  rgt' _ _ = P.Right
  (|||) = P.either

instance HasBinaryCoproducts U.UNIT where
  type U.U || U.U = U.U
  lft' U.Unit U.Unit = U.Unit
  rgt' U.Unit U.Unit = U.Unit
  U.Unit ||| U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (PRO j k) where
  type p || q = p :+: q
  lft' Prof{} Prof{} = Prof InjL
  rgt' Prof{} Prof{} = Prof InjR
  Prof l ||| Prof r = Prof (coproduct l r)

newtype COPROD k = COPR k
type instance UN COPR (COPR k) = k

type Coprod :: CAT (COPROD k)
data Coprod a b where
  Coprod :: (Ob a, Ob b) => {getCoprod :: UN COPR a ~> UN COPR b} -> Coprod a b

mkCoprod :: (CategoryOf k) => (a :: k) ~> b -> Coprod (COPR a) (COPR b)
mkCoprod f = Coprod f \\ f

instance (CategoryOf k) => Profunctor (Coprod :: CAT (COPROD k)) where
  dimap = dimapDefault
  r \\ Coprod f = r \\ f
instance (CategoryOf k) => Promonad (Coprod :: CAT (COPROD k)) where
  id = Coprod id
  Coprod f . Coprod g = Coprod (f . g)
instance (CategoryOf k) => CategoryOf (COPROD k) where
  type (~>) = Coprod
  type Ob a = (Is COPR a, Ob (UN COPR a))

instance (HasCoproducts k) => Monoidal (COPROD k) where
  type Unit = COPR InitialObject
  type a ** b = COPR (UN COPR a || UN COPR b)
  Coprod f `par` Coprod g = mkCoprod (f +++ g)
  leftUnitor (Coprod f) = mkCoprod (initiate' (tgt f) ||| f)
  leftUnitorInv (Coprod f) = mkCoprod (rgt' (obj @InitialObject) (tgt f) . f)
  rightUnitor (Coprod f) = mkCoprod (f ||| initiate' (tgt f))
  rightUnitorInv (Coprod f) = mkCoprod (lft' (tgt f) (obj @InitialObject) . f)
  associator (Coprod a) (Coprod b) (Coprod c) = mkCoprod ((a +++ lft' b c) ||| (rgt' a (b +++ c) . rgt' b c) \\ (a +++ b))
  associatorInv (Coprod a) (Coprod b) (Coprod c) = mkCoprod ((lft' (a +++ b) c . lft' a b) ||| (rgt' a b +++ c) \\ (a +++ b))

instance (HasCoproducts k) => SymMonoidal (COPROD k) where
  swap' (Coprod a) (Coprod b) = mkCoprod (rgt' b a ||| lft' b a)

instance (HasCoproducts k) => MonoidalProfunctor (Coprod :: CAT (COPROD k)) where
  lift0 = id
  lift2 = par
