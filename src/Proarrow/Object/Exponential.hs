{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Exponential where

import Data.Kind (Type)
import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , associator
  , leftUnitor
  , unitObj, swapInner'
  )
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

eval' :: (Closed k) => a ~> a' -> b ~> b' -> ((a' :: k) ~~> b) ** a ~> b'
eval' a b = let ab = b ^^^ tgt a in uncurry' (tgt a) (tgt b) (tgt ab) . (ab `par` a)

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
  => p a (x ~~> y)
  -> p a x
  -> p a y
ap pf px = let a = src pf in dimap (a &&& a) (eval' (tgt px) (obj @y)) (pf `par` px)

type Dual a = a ~~> Bottom

dual :: forall {k} (a :: k) a'. (StarAutonomous k) => a ~> a' -> Dual a' ~> Dual a
dual a = bottomObj ^^^ a

dualObj :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Obj (Dual a)
dualObj = dual (obj @a)

class (Closed k) => StarAutonomous k where
  type Bottom :: k
  bottomObj :: Obj (Bottom :: k)
  doubleNeg' :: (a :: k) ~> a' -> Dual (Dual a) ~> a'

doubleNeg :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
doubleNeg = doubleNeg' (obj @a)

doubleNegInv' :: (Closed k, SymMonoidal k) => (a :: k) ~> a' -> b ~> b' -> a ~> (a' ~~> b) ~~> b'
doubleNegInv' a b = let a'b = (src b ^^^ tgt a) in curry' (src a) a'b (eval' (tgt a) b . swap' a a'b)

dualityCounit' :: forall {k} a. (StarAutonomous k) => Obj a -> Dual a ** a ~> (Bottom :: k)
dualityCounit' a = eval' a bottomObj

dualityCounit :: forall {k} a. (SymMonoidal k, StarAutonomous k, Ob a) => Dual a ** a ~> (Bottom :: k)
dualityCounit = dualityCounit' (obj @a)

instance StarAutonomous () where
  type Bottom = '()
  bottomObj = U.Unit
  doubleNeg' U.Unit = U.Unit

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  type Bottom = '(Bottom, Bottom)
  bottomObj = bottomObj :**: bottomObj
  doubleNeg' (a :**: b) = doubleNeg' a :**: doubleNeg' b

class ((Bottom :: k) P.~ Unit, StarAutonomous k, SymMonoidal k) => CompactClosed k where
  distribDual' :: (a :: k) ~> a' -> b ~> b' -> Dual (a' ** b') ~> Dual a ** Dual b

combineDual' :: (CompactClosed k) => (a :: k) ~> a' -> b ~> b' -> Dual a' ** Dual b' ~> Dual (a ** b)
combineDual' a b = let dualA = dual (tgt a); dualB = dual (tgt b) in
  curry' (dualA `par` dualB) (src a `par` src b) (leftUnitor unitObj . (eval' a unitObj `par` eval' b unitObj) . swapInner' dualA dualB (src a) (src b))

distribDual :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => Dual (a ** b) ~> Dual a ** Dual b
distribDual = distribDual' (obj @a) (obj @b)

combineDual :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDual = combineDual' (obj @a) (obj @b)

dualityUnit' :: forall {k} a. (CompactClosed k) => Obj a -> (Unit :: k) ~> a ** Dual a
dualityUnit' a =
  let dualA = dual a
  in (doubleNeg' a `par` dualA) . distribDual' dualA a . (unitObj ^^^ dualityCounit' a) . mkExponential unitObj

dualityUnit :: forall {k} a. (CompactClosed k, Ob a) => (Unit :: k) ~> a ** Dual a
dualityUnit = dualityUnit' (obj @a)

compactClosedTrace'
  :: forall {k} x x' y y' u u'
   . (CompactClosed k)
  => (x :: k) ~> x'
  -> y ~> y'
  -> u ~> u'
  -> x' ** u' ~> y ** u
  -> x ~> y'
compactClosedTrace' x y u f =
  let dualU = unitObj ^^^ u
  in rightUnitor y
      . (src y `par` (dualityCounit @(Dual u') . (doubleNegInv' u unitObj `par` src dualU)))
      . associator (src y) (src u) (src dualU)
      . (f `par` src dualU)
      . associatorInv (tgt x) (tgt u) (src dualU)
      . (tgt x `par` dualityUnit @u')
      . rightUnitorInv x
      \\ dualU
      \\ u

instance CompactClosed () where
  distribDual' U.Unit U.Unit = U.Unit

instance (CompactClosed j, CompactClosed k) => CompactClosed (j, k) where
  distribDual' (a :**: b) (c :**: d) = distribDual' a c :**: distribDual' b d
