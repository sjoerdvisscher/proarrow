{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Dual where

import Prelude qualified as P

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal
  ( Monoidal (..)
  , MonoidalProfunctor (..)
  , SymMonoidal (..)
  , associator
  , leftUnitor
  , swapInner'
  , unitObj
  )
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), tgt)
import Proarrow.Object (Obj, obj, src)
import Proarrow.Object.Exponential (Closed (..), eval', mkExponential)

type Dual a = a ~~> Bottom

dual' :: forall {k} (a :: k) a'. (StarAutonomous k) => a ~> a' -> Dual a' ~> Dual a
dual' a = bottomObj ^^^ a

dual :: forall {k} (a :: k). (StarAutonomous k, Ob a) => Obj (Dual a)
dual = dual' (obj @a)

class (Closed k) => StarAutonomous k where
  {-# MINIMAL bottomObj, (doubleNeg | doubleNeg') #-}
  type Bottom :: k
  bottomObj :: Obj (Bottom :: k)
  doubleNeg :: forall (a :: k). (StarAutonomous k, Ob a) => Dual (Dual a) ~> a
  doubleNeg = doubleNeg' (obj @a)
  doubleNeg' :: forall (a :: k) a'. a ~> a' -> Dual (Dual a) ~> a'
  doubleNeg' a = a . doubleNeg @k @a \\ a

doubleNegInv' :: (Closed k, SymMonoidal k) => (a :: k) ~> a' -> b ~> b' -> a ~> (a' ~~> b) ~~> b'
doubleNegInv' a b = let a'b = (src b ^^^ tgt a) in curry' (src a) a'b (eval' (tgt a) b . swap' a a'b)

dualityCounit' :: forall {k} a. (StarAutonomous k) => Obj a -> Dual a ** a ~> (Bottom :: k)
dualityCounit' a = eval' a bottomObj

dualityCounit :: forall {k} a. (SymMonoidal k, StarAutonomous k, Ob a) => Dual a ** a ~> (Bottom :: k)
dualityCounit = dualityCounit' (obj @a)

instance StarAutonomous () where
  type Bottom = '()
  bottomObj = U.Unit
  doubleNeg = U.Unit

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  type Bottom = '(Bottom, Bottom)
  bottomObj = bottomObj :**: bottomObj
  doubleNeg = doubleNeg :**: doubleNeg

class ((Bottom :: k) P.~ Unit, StarAutonomous k, SymMonoidal k) => CompactClosed k where
  {-# MINIMAL (distribDual | distribDual') #-}
  distribDual :: forall (a :: k) b. (Ob a, Ob b) => Dual (a ** b) ~> Dual a ** Dual b
  distribDual = distribDual' (obj @a) (obj @b)
  distribDual' :: forall a a' b b'. (a :: k) ~> a' -> b ~> b' -> Dual (a' ** b') ~> Dual a ** Dual b
  distribDual' a b = (dual' a `par` dual' b) . distribDual @_ @a' @b' \\ a \\ b

combineDual' :: (CompactClosed k) => (a :: k) ~> a' -> b ~> b' -> Dual a' ** Dual b' ~> Dual (a ** b)
combineDual' a b =
  let dualA = dual' (tgt a); dualB = dual' (tgt b)
  in curry'
      (dualA `par` dualB)
      (src a `par` src b)
      (leftUnitor unitObj . (eval' a unitObj `par` eval' b unitObj) . swapInner' dualA dualB (src a) (src b))

combineDual :: forall {k} a b. (CompactClosed k, Ob (a :: k), Ob b) => Dual a ** Dual b ~> Dual (a ** b)
combineDual = combineDual' (obj @a) (obj @b)

dualityUnit' :: forall {k} a. (CompactClosed k) => Obj a -> (Unit :: k) ~> a ** Dual a
dualityUnit' a =
  let dualA = dual' a
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
  distribDual = U.Unit

instance (CompactClosed j, CompactClosed k) => CompactClosed (j, k) where
  distribDual @'(a, a') @'(b, b') = distribDual @j @a @b :**: distribDual @k @a' @b'
