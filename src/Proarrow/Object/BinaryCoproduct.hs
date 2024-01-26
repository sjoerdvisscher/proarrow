{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Core (CAT, PRO, CategoryOf(..), Promonad (..), Profunctor(..), UN, Is, dimapDefault)
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Profunctor.Coproduct ((:+:)(..), coproduct)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal(..))


class CategoryOf k => HasBinaryCoproducts k where
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
  Coprod :: (Ob a, Ob b) => UN COPR a ~> UN COPR b -> Coprod a b

mkCoprod :: CategoryOf k => (a :: k) ~> b -> Coprod (COPR a) (COPR b)
mkCoprod f = Coprod f \\ f

instance CategoryOf k => Profunctor (Coprod :: CAT (COPROD k)) where
  dimap = dimapDefault
  r \\ Coprod f = r \\ f
instance CategoryOf k => Promonad (Coprod :: CAT (COPROD k)) where
  id = Coprod id
  Coprod f . Coprod g = Coprod (f . g)
instance CategoryOf k => CategoryOf (COPROD k) where
  type (~>) = Coprod
  type Ob a = (Is COPR a, Ob (UN COPR a))

instance HasCoproducts k => Monoidal (COPROD k) where
  type Unit = COPR InitialObject
  type a ** b = COPR (UN COPR a || UN COPR b)
  Coprod f `par` Coprod g = mkCoprod (f +++ g)
  leftUnitor (Coprod a) = mkCoprod (initiate' a ||| a)
  leftUnitorInv (Coprod a) = mkCoprod (rgt' (obj @InitialObject) a)
  rightUnitor (Coprod a) = mkCoprod (a ||| initiate' a)
  rightUnitorInv (Coprod a) = mkCoprod (lft' a (obj @InitialObject))
  associator (Coprod a) (Coprod b) (Coprod c) = mkCoprod ((a +++ lft' b c) ||| (rgt' a (b +++ c) . rgt' b c) \\ (a +++ b))
  associatorInv (Coprod a) (Coprod b) (Coprod c) = mkCoprod ((lft' (a +++ b) c . lft' a b) ||| (rgt' a b +++ c) \\ (a +++ b))
