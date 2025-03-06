{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Exponential where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), associator, leftUnitor)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), PRO, Profunctor (..), Promonad (..), UN, (//))
import Proarrow.Object (Obj, obj)
import Proarrow.Object.BinaryCoproduct (HasCoproducts)
import Proarrow.Object.BinaryProduct (Cartesian, PROD (..), Prod (..), diag)
import Proarrow.Profunctor.Exponential ((:~>:) (..))
import Proarrow.Profunctor.Product ((:*:) (..))
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

infixr 2 ~~>

class (Monoidal k) => Closed k where
  type (a :: k) ~~> (b :: k) :: k
  withObExp :: (Ob (a :: k), Ob b) => ((Ob (a ~~> b)) => r) -> r
  curry :: (Ob (a :: k), Ob b) => a ** b ~> c -> a ~> b ~~> c
  uncurry :: (Ob (b :: k), Ob c) => a ~> b ~~> c -> a ** b ~> c
  (^^^) :: forall (a :: k) b x y. b ~> y -> x ~> a -> a ~~> b ~> x ~~> y
  f ^^^ g =
    f //
      g //
        withObExp @k @a @b P.$
          let ab = obj @(a ~~> b) in curry @k @(a ~~> b) @x (f . uncurry @_ @a @b ab . (ab `par` g))

curry' :: forall {k} a b c. (Closed k) => Obj (a :: k) -> Obj b -> a ** b ~> c -> a ~> b ~~> c
curry' a b = curry @k @a @b \\ a \\ b

uncurry' :: forall {k} b c a. (Closed k) => Obj (b :: k) -> Obj c -> a ~> b ~~> c -> a ** b ~> c
uncurry' b c = uncurry @k @b @c \\ b \\ c

comp :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b, Ob c) => (b ~~> c) ** (a ~~> b) ~> a ~~> c
comp =
  withObExp @k @b @c P.$
    withObExp @k @a @b P.$
      withOb2 @k @(b ~~> c) @(a ~~> b) P.$
        curry @_ @_ @a (eval @b @c . (obj @(b ~~> c) `par` eval @a @b) . associator @k @(b ~~> c) @(a ~~> b) @a)

mkExponential :: forall {k} a b. (Closed k) => (a :: k) ~> b -> Unit ~> (a ~~> b)
mkExponential ab = curry @_ @_ @a (ab . leftUnitor) \\ ab

lower :: forall {k} (a :: k) b. (Closed k, Ob a, Ob b) => (Unit ~> (a ~~> b)) -> a ~> b
lower f = uncurry @k @a @b f . leftUnitorInv

eval :: forall {k} a b. (Closed k, Ob a, Ob b) => ((a :: k) ~~> b) ** a ~> b
eval = withObExp @k @a @b (uncurry @k @a @b @(a ~~> b) id)

instance Closed Type where
  type a ~~> b = a -> b
  withObExp r = r
  curry = P.curry
  uncurry = P.uncurry
  (^^^) = P.flip dimap

instance Closed () where
  type '() ~~> '() = '()
  withObExp r = r
  curry U.Unit = U.Unit
  uncurry U.Unit = U.Unit
  U.Unit ^^^ U.Unit = U.Unit

instance (CategoryOf j, CategoryOf k) => Closed (PROD (PRO j k)) where
  type p ~~> q = PR (UN PR p :~>: UN PR q)
  withObExp r = r
  curry (Prod (Prof n)) = Prod (Prof \p -> p // Exp \ca bd q -> n (dimap ca bd p :*: q))
  uncurry (Prod (Prof n)) = Prod (Prof \(p :*: q) -> case n p of Exp f -> f id id q \\ q)
  Prod (Prof m) ^^^ Prod (Prof n) = Prod (Prof \(Exp f) -> Exp \ca bd p -> m (f ca bd (n p)))

instance (Closed j, Closed k) => Closed (j, k) where
  type '(a1, a2) ~~> '(b1, b2) = '(a1 ~~> b1, a2 ~~> b2)
  withObExp @'(a1, a2) @'(b1, b2) r = withObExp @j @a1 @b1 (withObExp @k @a2 @b2 r)
  curry @'(a1, a2) @'(b1, b2) (f1 :**: f2) = curry @j @a1 @b1 f1 :**: curry @k @a2 @b2 f2
  uncurry @'(a1, a2) @'(b1, b2) (f1 :**: f2) = uncurry @j @a1 @b1 f1 :**: uncurry @k @a2 @b2 f2
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

class (CCC k, HasCoproducts k) => BiCCC k
instance (CCC k, HasCoproducts k) => BiCCC k

ap
  :: forall {j} {k} y a x p
   . (Cartesian j, Closed k, MonoidalProfunctor (p :: PRO j k), Ob y)
  => p a (x ~~> y)
  -> p a x
  -> p a y
ap pf px = dimap diag (eval @x @y) (pf `par` px) \\ px
