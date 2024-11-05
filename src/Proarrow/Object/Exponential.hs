{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Exponential where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), associator, leftUnitor)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, tgt, (//))
import Proarrow.Object (Obj, obj, src)
import Proarrow.Object.BinaryProduct (Cartesian, HasBinaryProducts (..), PROD (..), Prod (..))
import Proarrow.Profunctor.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Product ((:*:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

infixr 2 ~~>

class (Monoidal k) => Closed k where
  type (a :: k) ~~> (b :: k) :: k
  curry' :: Obj (a :: k) -> Obj b -> a ** b ~> c -> a ~> b ~~> c
  uncurry' :: Obj (b :: k) -> Obj c -> a ~> b ~~> c -> a ** b ~> c
  (^^^) :: (b :: k) ~> y -> x ~> a -> a ~~> b ~> x ~~> y

curry :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b) => a ** b ~> c -> a ~> b ~~> c
curry = curry' (obj @a) (obj @b)

uncurry :: forall {k} (a :: k) b c. (Closed k, Ob b, Ob c) => a ~> b ~~> c -> a ** b ~> c
uncurry = uncurry' (obj @b) (obj @c)

comp :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b, Ob c) => (b ~~> c) ** (a ~~> b) ~> a ~~> c
comp =
  let a = obj @a; b2c = obj @c ^^^ obj @b; a2b = obj @b ^^^ a
  in curry @_ @a @c (eval @b @c . (b2c `par` eval @a @b) . associator b2c a2b a)
      \\ a2b
      \\ b2c
      \\ (b2c `par` a2b)

mkExponential :: forall {k} a b. (Closed k) => (a :: k) ~> b -> Unit ~> (a ~~> b)
mkExponential ab = curry @_ @a (ab . leftUnitor (src ab)) \\ ab \\ (par0 :: (Unit :: k) ~> Unit)

eval' :: (Closed k) => Obj a -> Obj b -> ((a :: k) ~~> b) ** a ~> b
eval' a b = uncurry' a b (b ^^^ a)

eval :: forall {k} a b. (Closed k, Ob a, Ob b) => ((a :: k) ~~> b) ** a ~> b
eval = eval' (obj @a) (obj @b)

instance Closed Type where
  type a ~~> b = a -> b
  curry' _ _ = P.curry
  uncurry' _ _ = P.uncurry
  (^^^) = P.flip dimap

instance Closed () where
  type '() ~~> '() = '()
  curry' U.Unit U.Unit U.Unit = U.Unit
  uncurry' U.Unit U.Unit U.Unit = U.Unit
  U.Unit ^^^ U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => Closed (PROD (PRO j k)) where
  type p ~~> q = PR (UN PR p :~>: UN PR q)
  curry' (Prod Prof{}) (Prod Prof{}) (Prod (Prof n)) = Prod (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q))
  uncurry' (Prod Prof{}) (Prod Prof{}) (Prod (Prof n)) = Prod (Prof \(p :*: q) -> case n p of Exp f -> f id id q \\ q)
  Prod (Prof m) ^^^ Prod (Prof n) = Prod (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p)))

instance (Closed j, Closed k) => Closed (j, k) where
  type '(a1, a2) ~~> '(b1, b2) = '(a1 ~~> b1, a2 ~~> b2)
  curry' (a1 :**: a2) (b1 :**: b2) (f1 :**: f2) = curry' a1 b1 f1 :**: curry' a2 b2 f2
  uncurry' (a1 :**: a2) (b1 :**: b2) (f1 :**: f2) = uncurry' a1 b1 f1 :**: uncurry' a2 b2 f2
  (f1 :**: f2) ^^^ (g1 :**: g2) = (f1 ^^^ g1) :**: (f2 ^^^ g2)

type ExponentialFunctor :: PRO k (OPPOSITE k, k)
data ExponentialFunctor a b where
  ExponentialFunctor :: (Ob c, Ob d) => a ~> (c ~~> d) -> ExponentialFunctor a '(OP c, d)

instance (Closed k) => Profunctor (ExponentialFunctor :: PRO k (OPPOSITE k, k)) where
  dimap = dimapRep
  r \\ ExponentialFunctor f = r \\ f

instance (Closed k) => Representable (ExponentialFunctor :: PRO k (OPPOSITE k, k)) where
  type ExponentialFunctor % '(OP a, b) = a ~~> b
  index (ExponentialFunctor f) = f
  tabulate = ExponentialFunctor
  repMap (Op f :**: g) = g ^^^ f

class (Cartesian k, Closed k) => CCC k
instance (Cartesian k, Closed k) => CCC k

ap
  :: forall {j} {k} y a x p
   . (Cartesian j, Closed k, MonoidalProfunctor (p :: PRO j k), Ob y)
  => p a (x ~~> y) -> p a x -> p a y
ap pf px = let a = src pf in dimap (a &&& a) (eval' (tgt px) (obj @y)) (pf `par` px)
