{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Exponential where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), associator, leftUnitor)
import Proarrow.Category.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), obj, (//), type (+->))
import Proarrow.Object.BinaryCoproduct (HasCoproducts)
import Proarrow.Object.BinaryProduct (Cartesian, diag)
import Proarrow.Profunctor.Representable (Representable (..), dimapRep)

infixr 2 ~~>

class (Monoidal k) => Closed k where
  type (a :: k) ~~> (b :: k) :: k
  withObExp :: (Ob (a :: k), Ob b) => ((Ob (a ~~> b)) => r) -> r
  curry :: (Ob (a :: k), Ob b) => a ** b ~> c -> a ~> b ~~> c
  apply :: (Ob (a :: k), Ob b) => (a ~~> b) ** a ~> b
  (^^^) :: forall (a :: k) b x y. b ~> y -> x ~> a -> a ~~> b ~> x ~~> y
  f ^^^ g =
    f //
      g //
        withObExp @k @a @b P.$
          let ab = obj @(a ~~> b) in curry @k @(a ~~> b) @x (f . apply @k @a @b . (ab `par` g))

uncurry :: forall {k} b c (a :: k). (Closed k) => (Ob b, Ob c) => a ~> b ~~> c -> a ** b ~> c
uncurry f = apply @k @b @c . (f `par` obj @b)

comp :: forall {k} (a :: k) b c. (Closed k, Ob a, Ob b, Ob c) => (b ~~> c) ** (a ~~> b) ~> a ~~> c
comp =
  withObExp @k @b @c P.$
    withObExp @k @a @b P.$
      withOb2 @k @(b ~~> c) @(a ~~> b) P.$
        curry @_ @_ @a (apply @k @b @c . (obj @(b ~~> c) `par` apply @k @a @b) . associator @k @(b ~~> c) @(a ~~> b) @a)

mkExponential :: forall {k} a b. (Closed k) => (a :: k) ~> b -> Unit ~> (a ~~> b)
mkExponential ab = curry @_ @_ @a (ab . leftUnitor) \\ ab

lower :: forall {k} (a :: k) b. (Closed k, Ob a, Ob b) => (Unit ~> (a ~~> b)) -> a ~> b
lower f = uncurry @a @b f . leftUnitorInv

instance Closed Type where
  type a ~~> b = a -> b
  withObExp r = r
  curry = P.curry
  apply = P.uncurry id
  (^^^) = P.flip dimap

instance Closed () where
  type '() ~~> '() = '()
  withObExp r = r
  curry U.Unit = U.Unit
  apply = U.Unit
  U.Unit ^^^ U.Unit = U.Unit

instance (Closed j, Closed k) => Closed (j, k) where
  type '(a1, a2) ~~> '(b1, b2) = '(a1 ~~> b1, a2 ~~> b2)
  withObExp @'(a1, a2) @'(b1, b2) r = withObExp @j @a1 @b1 (withObExp @k @a2 @b2 r)
  curry @'(a1, a2) @'(b1, b2) (f1 :**: f2) = curry @j @a1 @b1 f1 :**: curry @k @a2 @b2 f2
  apply @'(a1, a2) @'(b1, b2) = apply @j @a1 @b1 :**: apply @k @a2 @b2
  (f1 :**: f2) ^^^ (g1 :**: g2) = (f1 ^^^ g1) :**: (f2 ^^^ g2)

type ExponentialFunctor :: (OPPOSITE k, k) +-> k
data ExponentialFunctor a b where
  ExponentialFunctor :: (Ob c, Ob d) => a ~> (c ~~> d) -> ExponentialFunctor a '(OP c, d)

instance (Closed k) => Profunctor (ExponentialFunctor :: (OPPOSITE k, k) +-> k) where
  dimap = dimapRep
  r \\ ExponentialFunctor f = r \\ f

instance (Closed k) => Representable (ExponentialFunctor :: (OPPOSITE k, k) +-> k) where
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
   . (Closed j, Cartesian k, MonoidalProfunctor (p :: j +-> k), Ob y)
  => p a (x ~~> y)
  -> p a x
  -> p a y
ap pf px = dimap diag (apply @j @x @y) (pf `par` px) \\ px
