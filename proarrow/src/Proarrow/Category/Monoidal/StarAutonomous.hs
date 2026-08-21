{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Proarrow.Category.Monoidal.StarAutonomous where

import Prelude qualified as P

import Proarrow.Category.Instance.Free (Elem, FREE (..), Free (..), HasStructure (..), IsFreeOb (..), WithShow)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit qualified as U
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), swap, type (**!))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Obj, Profunctor (..), Promonad (..), obj)
import Proarrow.Optic (Iso, iso)

class (SymMonoidal k, Closed k, Ob (Unit :: k)) => StarAutonomous k where
  type Dual (a :: k) :: k
  withObDual :: (Ob (a :: k)) => ((Ob (Dual a)) => r) -> r
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
linDistS f@Str{} = withOb2 @k @b @c (withObDual @k @(b ** c) (Str (linDist @k @a @b @c (unStr f))))

linDistInvS
  :: forall {k} (a :: k) (b :: k) c. (StarAutonomous k, Ob b, Ob c) => '[a] ~> '[Dual (b ** c)] -> '[a, b] ~> '[Dual c]
linDistInvS f@Str{} = withObDual @k @c (Str (linDistInv @k @a @b @c (unStr f)))

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
  withObDual r = r
  dual U.Unit = U.Unit
  dualInv U.Unit = U.Unit
  linDist U.Unit = U.Unit
  linDistInv U.Unit = U.Unit

instance (StarAutonomous j, StarAutonomous k) => StarAutonomous (j, k) where
  type Dual '(a, b) = '(Dual a, Dual b)
  withObDual @'(a, b) r = withObDual @j @a (withObDual @k @b r)
  dual (f :**: g) = dual f :**: dual g
  dualInv (f :**: g) = dualInv f :**: dualInv g
  linDist @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDist @j @a1 @b1 @c1 f :**: linDist @k @a2 @b2 @c2 g
  linDistInv @'(a1, a2) @'(b1, b2) @'(c1, c2) (f :**: g) = linDistInv @j @a1 @b1 @c1 f :**: linDistInv @k @a2 @b2 @c2 g

data family DualF (a :: k) :: k
instance (Ob (a :: FREE cs p), StarAutonomous `Elem` cs) => IsFreeOb (DualF a) where
  type Lower f (DualF a) = Dual (Lower f a)
  withLowerOb @f r = withLowerOb @a @f (withObDual @_ @(Lower f a) r)
instance
  (Monoidal `Elem` cs, SymMonoidal `Elem` cs, Closed `Elem` cs, StarAutonomous `Elem` cs)
  => HasStructure cs p StarAutonomous
  where
  data Struct StarAutonomous a b where
    Dual :: a ~> b -> Struct StarAutonomous (DualF b) (DualF a)
    DualInv :: (Ob a, Ob b) => DualF a ~> DualF b -> Struct StarAutonomous b a
    LinDist :: (Ob a, Ob b, Ob c) => a **! b ~> DualF c -> Struct StarAutonomous a (DualF (b **! c))
    LinDistInv :: (Ob a, Ob b, Ob c) => a ~> DualF (b **! c) -> Struct StarAutonomous (a **! b) (DualF c)
  foldStructure go (Dual f) = dual (go f)
  foldStructure @f go (DualInv @a @b g) =
    withLowerOb @a @f (withLowerOb @b @f (dualInv @_ @(Lower f a) @(Lower f b) (go g)))
  foldStructure @f go (LinDist @a @b @c g) =
    withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c @f (linDist @_ @(Lower f a) @(Lower f b) @(Lower f c) (go g))))
  foldStructure @f go (LinDistInv @a @b @c g) =
    withLowerOb @a @f (withLowerOb @b @f (withLowerOb @c @f (linDistInv @_ @(Lower f a) @(Lower f b) @(Lower f c) (go g))))
deriving instance (WithShow a) => P.Show (Struct StarAutonomous a b)

instance
  ( Monoidal (FREE cs p)
  , SymMonoidal (FREE cs p)
  , Closed (FREE cs p)
  , Monoidal `Elem` cs
  , SymMonoidal `Elem` cs
  , Closed `Elem` cs
  , StarAutonomous `Elem` cs
  )
  => StarAutonomous (FREE cs p)
  where
  type Dual a = DualF a
  withObDual r = r
  dual f = St (Dual f) Id \\ f
  dualInv @a @b f = St (DualInv @a @b f) Id \\ f
  linDist @a @b @c f = St (LinDist @a @b @c f) Id \\ f
  linDistInv @a @b @c f = St (LinDistInv @a @b @c f) Id \\ f
