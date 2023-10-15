{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Tensor(..), TENSOR)
import Proarrow.Core (PRO, CategoryOf, Category (..), Profunctor(..), type (~>))
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Initial (HasInitialObject(..))
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Profunctor.Coproduct ((:+:)(..), coproduct)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Unit (UNIT(..), Unit(..))


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

instance HasBinaryCoproducts UNIT where
  type 'U || 'U = 'U
  lft' Unit Unit = Unit
  rgt' Unit Unit = Unit
  Unit ||| Unit = Unit

instance (CategoryOf j, CategoryOf k) => HasBinaryCoproducts (PRO j k) where
  type p || q = p :+: q
  lft' Prof{} Prof{} = Prof InjL
  rgt' Prof{} Prof{} = Prof InjR
  Prof l ||| Prof r = Prof (coproduct l r)



type CoproductFunctor :: TENSOR k
data CoproductFunctor a b where
  CoproductFunctor :: forall a c d. (Ob c, Ob d) => a ~> (c || d) -> CoproductFunctor a '(c, d)

instance HasBinaryCoproducts k => Profunctor (CoproductFunctor :: TENSOR k) where
  dimap l (r1 :**: r2) (CoproductFunctor f) = CoproductFunctor ((r1 +++ r2) . f . l) \\ r1 \\ r2
  r \\ CoproductFunctor f = r \\ f

instance HasBinaryCoproducts k => Representable (CoproductFunctor :: TENSOR k) where
  type CoproductFunctor % '(a, b) = a || b
  index (CoproductFunctor f) = f
  tabulate = CoproductFunctor
  repMap (f :**: g) = f +++ g

instance HasCoproducts k => Tensor (CoproductFunctor :: TENSOR k) where
  type U (CoproductFunctor :: TENSOR k) = InitialObject :: k
  leftUnitor a = initiate' a ||| a
  leftUnitorInv = rgt' (obj @(InitialObject :: k))
  rightUnitor a = a ||| initiate' a
  rightUnitorInv a = lft' a (obj @(InitialObject :: k))
  associator a b c = (a +++ lft' b c) ||| (rgt' a (b +++ c) . rgt' b c) \\ (a +++ b)
  associatorInv a b c = (lft' (a +++ b) c . lft' a b) ||| (rgt' a b +++ c) \\ (a +++ b)