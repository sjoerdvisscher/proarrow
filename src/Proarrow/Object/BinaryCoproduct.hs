{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.BinaryCoproduct where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Tensor(..))
import Proarrow.Core (PRO, CategoryOf, Category (..), Profunctor(..), type (~>))
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Initial (HasInitialObject(..), initiate)
import Proarrow.Profunctor.Representable (Representable(..))

class CategoryOf k => HasBinaryCoproducts k where
  type (a :: k) || (b :: k) :: k
  left' :: Obj (a :: k) -> Obj b -> a ~> (a || b)
  right' :: Obj (a :: k) -> Obj b -> b ~> (a || b)
  (|||) :: (x :: k) ~> a -> y ~> a -> (x || y) ~> a
  (+++) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a || b ~> x || y
  l +++ r = (left @x @y . l) ||| (right @x @y . r) \\ l \\ r

left :: forall {k} (a :: k) (b :: k). (HasBinaryCoproducts k, Ob a, Ob b) => a ~> (a || b)
left = left' (obj @a) (obj @b)
right :: forall {k} (a :: k) (b :: k). (HasBinaryCoproducts k, Ob a, Ob b) => b ~> (a || b)
right = right' (obj @a) (obj @b)

type HasCoproducts k = (HasInitialObject k, HasBinaryCoproducts k)

instance HasBinaryCoproducts Type where
  type a || b = P.Either a b
  left' _ _ = P.Left
  right' _ _ = P.Right
  (|||) = P.either


type CoproductFunctor :: PRO k (k, k)
data CoproductFunctor a b where
  CoproductFunctor :: (Ob c, Ob d) => a ~> (c || d) -> CoproductFunctor a '(c, d)

instance HasBinaryCoproducts k => Profunctor (CoproductFunctor :: PRO k (k, k)) where
  dimap l (r1 :**: r2) (CoproductFunctor f) = CoproductFunctor ((r1 +++ r2) . f . l) \\ r1 \\ r2
  r \\ CoproductFunctor f = r \\ f

instance HasBinaryCoproducts k => Representable (CoproductFunctor :: PRO k (k, k)) where
  type CoproductFunctor % '(a, b) = a || b
  index (CoproductFunctor f) = f
  tabulate = CoproductFunctor
  repMap (f :**: g) = f +++ g

instance HasCoproducts k => Tensor (CoproductFunctor :: PRO k (k, k)) where
  type U (CoproductFunctor :: PRO k (k, k)) = InitialObject :: k
  leftUnitor :: forall a. Ob (a :: k) => (CoproductFunctor % '(InitialObject, a)) ~> a
  leftUnitor = initiate @a ||| obj @a
  leftUnitorInv :: forall a. Ob (a :: k) => a ~> (CoproductFunctor % '(InitialObject, a))
  leftUnitorInv = right @(InitialObject :: k) @(a :: k)
  rightUnitor :: forall a. Ob (a :: k) => (CoproductFunctor % '(a, InitialObject)) ~> a
  rightUnitor = obj @a ||| initiate @a
  rightUnitorInv :: forall a. Ob (a :: k) => a ~> (CoproductFunctor % '(a, InitialObject))
  rightUnitorInv = left @(a :: k) @(InitialObject :: k)
  associator' a b c = (a +++ left' b c) ||| (right' a (b +++ c) . right' b c) \\ (a +++ b)
  associatorInv' a b c = (left' (a +++ b) c . left' a b) ||| (right' a b +++ c) \\ (a +++ b)