{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.Exponential where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Opposite (OPPOSITE(..), Op (..))
import Proarrow.Core (PRO, CategoryOf (..), Profunctor(..), Promonad(..), dimapDefault, (//))
import Proarrow.Object (Obj, obj, src)
import Proarrow.Object.BinaryProduct (HasProducts, HasBinaryProducts (..), ProductFunctor)
import Proarrow.Profunctor.Representable (Representable(..))
import Proarrow.Object.Terminal (El)
import Proarrow.Category.Monoidal (leftUnitor, associator)
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Profunctor.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Product ((:*:) (..))
import Proarrow.Category.Instance.Unit (UNIT(..), Unit(..))

infixr 2 ~~>

class (HasProducts k) => CartesianClosed k where
  type (a :: k) ~~> (b :: k) :: k
  curry' :: Obj (a :: k) -> Obj b -> a && b ~> c -> a ~> b ~~> c
  uncurry' :: Obj (b :: k) -> Obj c -> a ~> b ~~> c -> a && b ~> c
  (^^^) :: (b :: k) ~> y -> x ~> a -> a ~~> b ~> x ~~> y

curry :: forall {k} (a :: k) b c. (CartesianClosed k, Ob a, Ob b) => a && b ~> c -> a ~> b ~~> c
curry = curry' (obj @a) (obj @b)

uncurry :: forall {k} (a :: k) b c. (CartesianClosed k, Ob b, Ob c) => a ~> b ~~> c -> a && b ~> c
uncurry = uncurry' (obj @b) (obj @c)

comp :: forall {k} (a :: k) b c. (CartesianClosed k, Ob a, Ob b, Ob c) => (b ~~> c) && (a ~~> b) ~> a ~~> c
comp = let a = obj @a; b2c = obj @c ^^^ obj @b; a2b = obj @b ^^^ a in
  curry @_ @a @c (eval @b @c . (b2c *** eval @a @b) . associator @ProductFunctor b2c a2b a)
  \\ a2b \\ b2c \\ (b2c *** a2b)

mkExponential :: forall {k} a b. CartesianClosed k => (a :: k) ~> b -> El (a ~~> b)
mkExponential ab = curry @_ @a (ab . leftUnitor @ProductFunctor (src ab)) \\ ab

eval :: forall {k} a b. (CartesianClosed k, Ob a, Ob b) => ((a :: k) ~~> b) && a ~> b
eval = uncurry @_ @a @b (obj @b ^^^ obj @a)


instance CartesianClosed Type where
  type a ~~> b = a -> b
  curry' _ _ = P.curry
  uncurry' _ _ = P.uncurry
  (^^^) = P.flip dimapDefault

instance CartesianClosed UNIT where
  type U ~~> U = U
  curry' Unit Unit Unit = Unit
  uncurry' Unit Unit Unit = Unit
  Unit ^^^ Unit = Unit

instance (CategoryOf j, CategoryOf k) => CartesianClosed (PRO j k) where
  type p ~~> q = p :~>: q
  curry' Prof{} Prof{} (Prof n) = Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q)
  uncurry' Prof{} Prof{} (Prof n) = Prof \(p :*: q) -> case n p of Exp f -> f id id q \\ q
  Prof m ^^^ Prof n = Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p))



type ExponentialFunctor :: PRO k (OPPOSITE k, k)

data ExponentialFunctor a b where
  ExponentialFunctor :: (Ob c, Ob d) => a ~> (c ~~> d) -> ExponentialFunctor a '(OP c, d)

instance CartesianClosed k => Profunctor (ExponentialFunctor :: PRO k (OPPOSITE k, k)) where
  dimap l (Op r1 :**: r2) (ExponentialFunctor f) = ExponentialFunctor ((r2 ^^^ r1) . f . l) \\ r1 \\ r2
  r \\ ExponentialFunctor f = r \\ f

instance CartesianClosed k => Representable (ExponentialFunctor :: PRO k (OPPOSITE k, k)) where
  type ExponentialFunctor % '(OP a, b) = a ~~> b
  index (ExponentialFunctor f) = f
  tabulate = ExponentialFunctor
  repMap (Op f :**: g) = g ^^^ f
