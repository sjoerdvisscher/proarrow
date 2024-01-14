{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.BinaryProduct where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Monoidal (Tensor (..))
import Proarrow.Core (PRO, CategoryOf(..), Promonad (..), Profunctor(..))
import Proarrow.Object (Obj, obj)
import Proarrow.Object.Terminal (HasTerminalObject (..))
import Proarrow.Profunctor.Representable (Representable(..), dimapRep)
import Proarrow.Profunctor.Product ((:*:) (..), prod)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Unit (UNIT(..), Unit(..))

infixl 5 &&
infixl 5 &&&
infixl 5 ***

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


first :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (a && c) ~> (b && c)
first f = f *** obj @c

second :: forall {k} (c :: k) (a :: k) (b :: k). (HasBinaryProducts k, Ob c) => a ~> b -> (c && a) ~> (c && b)
second f = obj @c *** f


type HasProducts k = (HasTerminalObject k, HasBinaryProducts k)

instance HasBinaryProducts Type where
  type a && b = (a, b)
  fst' _ _ = P.fst
  snd' _ _ = P.snd
  f &&& g = \a -> (f a, g a)

instance HasBinaryProducts UNIT where
  type 'U && 'U = 'U
  fst' Unit Unit = Unit
  snd' Unit Unit = Unit
  Unit &&& Unit = Unit

instance (HasBinaryProducts j, HasBinaryProducts k) => HasBinaryProducts (j, k) where
  type '(a1, a2) && '(b1, b2) = '(a1 && b1, a2 && b2)
  fst' (a1 :**: a2) (b1 :**: b2) = fst' a1 b1 :**: fst' a2 b2
  snd' (a1 :**: a2) (b1 :**: b2) = snd' a1 b1 :**: snd' a2 b2
  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)

instance (CategoryOf j, CategoryOf k) => HasBinaryProducts (PRO j k) where
  type p && q = p :*: q
  fst' Prof{} Prof{} = Prof fstP
  snd' Prof{} Prof{} = Prof sndP
  Prof l &&& Prof r = Prof (prod l r)


type ProductFunctor :: PRO k (k, k)
data ProductFunctor a b where
  ProductFunctor :: forall a c d. (Ob c, Ob d) => a ~> (c && d) -> ProductFunctor a '(c, d)

instance HasBinaryProducts k => Profunctor (ProductFunctor :: PRO k (k, k)) where
  dimap = dimapRep
  r \\ ProductFunctor f = r \\ f

instance HasBinaryProducts k => Representable (ProductFunctor :: PRO k (k, k)) where
  type ProductFunctor % '(a, b) = a && b
  index (ProductFunctor f) = f
  tabulate = ProductFunctor
  repMap (f :**: g) = f *** g

instance HasProducts k => Tensor (ProductFunctor :: PRO k (k, k)) where
  type U (ProductFunctor :: PRO k (k, k)) = TerminalObject :: k
  leftUnitor = snd' (obj @(TerminalObject :: k))
  leftUnitorInv a = terminate' a &&& a
  rightUnitor a = fst' a (obj @(TerminalObject :: k))
  rightUnitorInv a = a &&& terminate' a
  associator a b c = (fst' a b . fst' (a *** b) c) &&& (snd' a b *** c) \\ (a *** b)
  associatorInv a b c = (a *** fst' b c) &&& (snd' b c . snd' a (b *** c)) \\ (a *** b)
