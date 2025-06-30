{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Dual where

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , associator
  , leftUnitorWith
  , rightUnitorInvWith
  , rightUnitorWith
  , swap
  )
import Proarrow.Category.Monoidal.Action (MonoidalAction (..), Strong (..))
import Proarrow.Core (CategoryOf (..), Obj, Profunctor (..), Promonad (..), obj)
import Proarrow.Object.Exponential (Closed (..))

class (SymMonoidal k, Closed k, Ob (Unit :: k)) => StarAutonomous k where
  type Dual (a :: k) :: k
  dual :: (a :: k) ~> b -> Dual b ~> Dual a
  dualInv :: (Ob (a :: k), Ob b) => Dual a ~> Dual b -> b ~> a
  linDist :: (Ob (a :: k), Ob b, Ob c) => a ** b ~> Dual c -> a ~> Dual (b ** c)
  linDistInv :: (Ob (a :: k), Ob b, Ob c) => a ~> Dual (b ** c) -> a ** b ~> Dual c

dualObj :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Obj (Dual a)
dualObj = dual (obj @a)

doubleNeg :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
doubleNeg = dualInv @k @a (doubleNegInv @(Dual a)) \\ dualObj @(Dual a) \\ dualObj @a

doubleNegInv :: forall {k} (a :: k). (StarAutonomous k, Ob a) => a ~> Dual (Dual a)
doubleNegInv =
  linDistInv @k @Unit @a @(Dual a) (dual (swap @k @a @(Dual a)) . dualityUnitSA @a) . leftUnitorInv @k @a
    \\ dualObj @a

type ExpSA a b = Dual (a ** Dual b)

currySA :: forall {k} (a :: k) b c. (StarAutonomous k, Ob a, Ob b) => a ** b ~> c -> a ~> ExpSA b c
currySA f = linDist @k @a @b @(Dual c) (doubleNegInv @c . f) \\ f \\ dual f

applySA :: forall {k} (b :: k) c. (StarAutonomous k, Ob b, Ob c) => ExpSA b c ** b ~> c
applySA =
  doubleNeg @c . withOb2 @k @b @(Dual c) (linDistInv @k @(ExpSA b c) @b @(Dual c) id \\ dualObj @(b ** Dual c))
    \\ dualObj @c

expSA :: forall {k} (a :: k) b x y. (StarAutonomous k) => b ~> y -> x ~> a -> ExpSA a b ~> ExpSA x y
expSA f g = dual (g `par` dual f)

dualityUnitSA :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Unit ~> Dual (Dual a ** a)
dualityUnitSA = linDist @k @_ @(Dual a) @a leftUnitor \\ dualObj @a

dualityCounitSA :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Dual a ** a ~> Dual Unit
dualityCounitSA = linDistInv @k @(Dual a) @a @Unit (dual (rightUnitor @k @a)) \\ dualObj @a

instance StarAutonomous () where
  type Dual '() = '()
  dual U.Unit = U.Unit
  dualInv U.Unit = U.Unit
  linDist U.Unit = U.Unit
  linDistInv U.Unit = U.Unit

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  type Dual '(a, b) = '(Dual a, Dual b)
  dual (f :**: g) = dual f :**: dual g
  dualInv (f :**: g) = dualInv f :**: dualInv g
  linDist @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDist @j @a1 @b1 @c1 f :**: linDist @k @a2 @b2 @c2 g
  linDistInv @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDistInv @j @a1 @b1 @c1 f :**: linDistInv @k @a2 @b2 @c2 g

class (StarAutonomous k, SymMonoidal k) => CompactClosed k where
  distribDual :: forall (a :: k) b. (Ob a, Ob b) => Dual (a ** b) ~> Dual a ** Dual b
  dualUnit :: Dual (Unit :: k) ~> Unit

dualityUnit :: forall {k} (a :: k). (CompactClosed k, Ob a) => Unit ~> a ** Dual a
dualityUnit = let dualA = dualObj @a in (doubleNeg @a `par` dualA) . distribDual @k @(Dual a) @a . dualityUnitSA @a \\ dualA

dualityCounit :: forall {k} (a :: k). (CompactClosed k, Ob a) => Dual a ** a ~> Unit
dualityCounit = dualUnit . dualityCounitSA @a

dualUnitInv :: forall {k}. (CompactClosed k) => (Unit :: k) ~> Dual Unit
dualUnitInv = leftUnitor @k @(Dual Unit) . dualityUnit @Unit \\ dualObj @(Unit :: k)

combineDual :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDual =
  withOb2 @k @(Dual a) @(Dual b)
    ( linDist @k @_ @a @b
        ( leftUnitorWith (dualityCounit @a . swap @k @a @(Dual a))
            . associatorInv @k @a @(Dual a) @(Dual b)
            . swap @k @(Dual a ** Dual b) @a
        )
    )
    \\ dualObj @a
    \\ dualObj @b

compactClosedTrace :: forall {k} u (x :: k) y. (CompactClosed k, Ob x, Ob y, Ob u) => x ** u ~> y ** u -> x ~> y
compactClosedTrace f =
  rightUnitorWith (dualityCounit @u . swap @k @u @(Dual u))
    . associator @k @y @u @(Dual u)
    . (f `par` obj @(Dual u))
    . associatorInv @k @x @u @(Dual u)
    . rightUnitorInvWith (dualityUnit @u)
    \\ dualObj @u

compactClosedCoact
  :: forall {m} {k} (u :: m) (x :: k) (y :: k)
   . (CompactClosed m, MonoidalAction m k, Ob x, Ob y, Ob u) => Act u x ~> Act u y -> x ~> y
compactClosedCoact f =
  unitor @m @k @y
    . act (dualityCounit @u) (obj @y)
    . multiplicator @m @k @(Dual u) @u @y
    . act (obj @(Dual u)) f
    . multiplicatorInv @m @k @(Dual u) @u @x
    . act (swap @m @u @(Dual u) . dualityUnit @u) (obj @x)
    . unitorInv @m @k @x
    \\ dualObj @u

instance CompactClosed () where
  distribDual = U.Unit
  dualUnit = U.Unit

instance (CompactClosed j, CompactClosed k) => CompactClosed (j, k) where
  distribDual @'(a, a') @'(b, b') = distribDual @j @a @b :**: distribDual @k @a' @b'
  dualUnit = dualUnit :**: dualUnit
