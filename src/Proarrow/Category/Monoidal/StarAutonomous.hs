{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Proarrow.Category.Monoidal.StarAutonomous where

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Obj, Profunctor (..), Promonad (..), obj)
import Proarrow.Optic (Iso, iso)

class (Ob (Dual a)) => ObDual a
instance (Ob (Dual a)) => ObDual a

class (SymMonoidal k, Closed k, Ob (Unit :: k), forall (a :: k). (Ob a) => ObDual a) => StarAutonomous k where
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

doubleNegIso
  :: forall {k} (a :: k) (a' :: k). (StarAutonomous k, Ob a, Ob a') => Iso a a' (Dual (Dual a)) (Dual (Dual a'))
doubleNegIso = iso doubleNegInv doubleNeg

linDistS
  :: forall {k} (a :: k) (b :: k) c. (StarAutonomous k, Ob c) => '[a, b] ~> '[Dual c] -> '[a] ~> '[Dual (b ** c)]
linDistS f@Str{} = withOb2 @k @b @c (Str (linDist @k @a @b @c (unStr f)))

linDistInvS
  :: forall {k} (a :: k) (b :: k) c. (StarAutonomous k, Ob b, Ob c) => '[a] ~> '[Dual (b ** c)] -> '[a, b] ~> '[Dual c]
linDistInvS f@Str{} = Str (linDistInv @k @a @b @c (unStr f))

type ExpSA a b = Dual (a ** Dual b)

currySA :: forall {k} (a :: k) b c. (StarAutonomous k, Ob a, Ob b) => a ** b ~> c -> a ~> ExpSA b c
currySA f = linDist @k @a @b @(Dual c) (doubleNegInv @c . f) \\ f \\ dual f

applySA :: forall {k} (b :: k) c. (StarAutonomous k, Ob b, Ob c) => ExpSA b c ** b ~> c
applySA =
  doubleNeg @c . withOb2 @k @b @(Dual c) (linDistInv @k @(ExpSA b c) @b @(Dual c) id \\ dualObj @(b ** Dual c))
    \\ dualObj @c

expSA :: forall {k} (a :: k) b x y. (StarAutonomous k) => b ~> y -> x ~> a -> ExpSA a b ~> ExpSA x y
expSA f g = dual (g ** dual f)

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
