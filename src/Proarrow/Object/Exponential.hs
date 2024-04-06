{-# LANGUAGE AllowAmbiguousTypes #-}
module Proarrow.Object.Exponential where

import Data.Kind (Type)
import qualified Prelude as P

import Proarrow.Category.Instance.Product ((:**:)(..))
import Proarrow.Category.Opposite (OPPOSITE(..), Op (..))
import Proarrow.Core (PRO, CategoryOf (..), Profunctor(..), Promonad(..), UN, (//), tgt)
import Proarrow.Object (Obj, obj, src)
import Proarrow.Profunctor.Representable (Representable(..), dimapRep)
import Proarrow.Category.Monoidal (leftUnitor, associator, Monoidal(..), MonoidalProfunctor (..))
import Proarrow.Category.Instance.Prof (Prof(..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Object.BinaryProduct (PROD(..), Prod (..), Cartesian, HasBinaryProducts (..))
import Proarrow.Profunctor.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Product ((:*:)(..))

infixr 2 ~~>

class Monoidal k => Closed k where
  type (a :: k) ~~> (b :: k) :: k
  curry' :: Obj (a :: k) -> Obj b -> a ** b ~> c -> a ~> b ~~> c
  uncurry' :: Obj (b :: k) -> Obj c -> a ~> b ~~> c -> a ** b ~> c
  (^^^) :: (b :: k) ~> y -> x ~> a -> a ~~> b ~> x ~~> y

curry :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b) => a ** b ~> c -> a ~> b ~~> c
curry = curry' (obj @a) (obj @b)

uncurry :: forall {k} (a :: k) b c. (Closed k, Ob b, Ob c) => a ~> b ~~> c -> a ** b ~> c
uncurry = uncurry' (obj @b) (obj @c)

comp :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b, Ob c) => (b ~~> c) ** (a ~~> b) ~> a ~~> c
comp = let a = obj @a; b2c = obj @c ^^^ obj @b; a2b = obj @b ^^^ a in
  curry @_ @a @c (eval @b @c . (b2c `par` eval @a @b) . associator b2c a2b a)
  \\ a2b \\ b2c \\ (b2c `par` a2b)

mkExponential :: forall {k} a b. Closed k => (a :: k) ~> b -> Unit ~> (a ~~> b)
mkExponential ab = curry @_ @a (ab . leftUnitor (src ab)) \\ ab

eval' :: Closed k => Obj a -> Obj b -> ((a :: k) ~~> b) ** a ~> b
eval' a b = uncurry' a b (b ^^^ a)

eval :: forall {k} a b. (Closed k, Ob a, Ob b) => ((a :: k) ~~> b) ** a ~> b
eval = eval' (obj @a) (obj @b)



instance Closed Type where
  type a ~~> b = a -> b
  curry' _ _ = P.curry
  uncurry' _ _ = P.uncurry
  (^^^) = P.flip dimap

instance Closed U.UNIT where
  type U.U ~~> U.U = U.U
  curry' U.Unit U.Unit U.Unit = U.Unit
  uncurry' U.Unit U.Unit U.Unit = U.Unit
  U.Unit ^^^ U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => Closed (PROD (PRO j k)) where
  type p ~~> q = PR (UN PR p :~>: UN PR q)
  curry' (Prod Prof{}) (Prod Prof{}) (Prod (Prof n)) = Prod (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q))
  uncurry' (Prod Prof{}) (Prod Prof{}) (Prod (Prof n)) = Prod (Prof \(p :*: q) -> case n p of Exp f -> f id id q \\ q)
  Prod (Prof m) ^^^ Prod (Prof n) = Prod (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p)))



type ExponentialFunctor :: PRO k (OPPOSITE k, k)

data ExponentialFunctor a b where
  ExponentialFunctor :: (Ob c, Ob d) => a ~> (c ~~> d) -> ExponentialFunctor a '(OP c, d)

instance Closed k => Profunctor (ExponentialFunctor :: PRO k (OPPOSITE k, k)) where
  dimap = dimapRep
  r \\ ExponentialFunctor f = r \\ f

instance Closed k => Representable (ExponentialFunctor :: PRO k (OPPOSITE k, k)) where
  type ExponentialFunctor % '(OP a, b) = a ~~> b
  index (ExponentialFunctor f) = f
  tabulate = ExponentialFunctor
  repMap (Op f :**: g) = g ^^^ f


ap
  :: forall {j} {k} y a x p
  . (Cartesian j, Closed k, MonoidalProfunctor (p :: PRO j k), Ob y)
  => p a (x ~~> y) -> p a x -> p a y
ap pf px = let a = src pf in dimap (a &&& a) (eval' (tgt px) (obj @y)) (lift2 pf px)