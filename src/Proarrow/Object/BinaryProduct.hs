{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.BinaryProduct where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Unit (Unit(..))
import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Tensor(..))
import Proarrow.Core (PRO, CategoryOf, Category (..), Profunctor(..), type (~>), (//))
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Terminal (HasTerminalObject (..), terminate)
import Proarrow.Profunctor.Representable (Representable(..))


class CategoryOf k => HasBinaryProducts k where
  type (a :: k) && (b :: k) :: k
  fst' :: Obj (a :: k) -> Obj b -> a && b ~> a
  snd' :: Obj (a :: k) -> Obj b -> a && b ~> b
  (&&&) :: (a :: k) ~> x -> a ~> y -> a ~> x && y
  (***) :: forall a b x y. (a :: k) ~> x -> b ~> y -> a && b ~> x && y
  l *** r = (l . fst @a @b) &&& (r . snd @a @b) \\ l \\ r

fst :: forall {k} (a :: k) (b :: k). (HasBinaryProducts k, Ob a, Ob b) => (a && b) ~> a
fst = fst' (obj @a) (obj @b)
snd :: forall {k} (a :: k) (b :: k). (HasBinaryProducts k, Ob a, Ob b) => (a && b) ~> b
snd = snd' (obj @a) (obj @b)

type HasProducts k = (HasTerminalObject k, HasBinaryProducts k)

instance HasBinaryProducts Type where
  type a && b = (a, b)
  fst' _ _ = P.fst
  snd' _ _ = P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts () where
  type '() && '() = '()
  fst' Unit Unit = Unit
  snd' Unit Unit = Unit
  Unit &&& Unit = Unit


type ProductFunctor :: PRO k (k, k)
data ProductFunctor a b where
  ProductFunctor :: (Ob c, Ob d) => a ~> (c && d) -> ProductFunctor a '(c, d)

instance HasBinaryProducts k => Profunctor (ProductFunctor :: PRO k (k, k)) where
  dimap l (r1 :**: r2) (ProductFunctor f) = r1 // r2 // ProductFunctor ((r1 *** r2) . f . l)
  r \\ ProductFunctor f = r \\ f

instance HasBinaryProducts k => Representable (ProductFunctor :: PRO k (k, k)) where
  type ProductFunctor % '(a, b) = a && b
  index (ProductFunctor f) = f
  tabulate = ProductFunctor
  repMap (f :**: g) = f *** g

instance HasProducts k => Tensor (ProductFunctor :: PRO k (k, k)) where
  type U (ProductFunctor :: PRO k (k, k)) = TerminalObject :: k
  leftUnitor :: forall a. Ob (a :: k) => (ProductFunctor % '(TerminalObject, a)) ~> a
  leftUnitor = snd @(TerminalObject :: k) @(a :: k)
  leftUnitorInv :: forall a. Ob (a :: k) => a ~> (ProductFunctor % '(TerminalObject, a))
  leftUnitorInv = terminate @a &&& obj @a
  rightUnitor :: forall a. Ob (a :: k) => (ProductFunctor % '(a, TerminalObject)) ~> a
  rightUnitor = fst @(a :: k) @(TerminalObject :: k)
  rightUnitorInv :: forall a. Ob (a :: k) => a ~> (ProductFunctor % '(a, TerminalObject))
  rightUnitorInv = obj @a &&& terminate @a
  associator' a b c = (fst' a b . fst' (a *** b) c) &&& (snd' a b *** c) \\ (a *** b)
  associatorInv' a b c = (a *** fst' b c) &&& (snd' b c . snd' a (b *** c)) \\ (a *** b)
