{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Object.Pullback where

import Prelude (($))

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), UN, lmap, obj, (//), type (+->))
import Proarrow.Object (pattern Objs)
import Proarrow.Object.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD (..), Prod (..))
import Proarrow.Object.Initial (HasZeroObject (..))
import Proarrow.Profunctor.List (LIST (..), List (..))

-- | A cone is a bunch of arrows with a shared source.
data Cone (a :: PROD k) (bs :: LIST k) where
  Apex :: (Ob a) => Cone (PR a) (L '[])
  Leg :: a ~> b -> Cone (PR a) (L bs) -> Cone (PR a) (L (b : bs))

instance (CategoryOf k) => Profunctor (Cone :: LIST k +-> PROD k) where
  dimap l Nil Apex = Apex \\ l
  dimap (Prod l) (Cons r rs) (Leg f fs) = Leg (r . f . l) (dimap (Prod l) rs fs)
  r \\ Apex = r
  r \\ Leg l Apex = r \\ l
  r \\ Leg l c@(Leg _ c1) = r \\ l \\ c \\ c1

instance (HasProducts k) => MonoidalProfunctor (Cone :: LIST k +-> PROD k) where
  one = Apex
  Apex @a ** rs = lmap (Prod (snd @_ @a)) rs \\ rs
  Leg l ls ** (rs :: Cone r rs) = Leg (l . fst @_ @_ @(UN PR r)) (ls ** rs) \\ l \\ rs

-- | A cosink (a.k.a a source) is a cone, but with the apex type hidden by an existential.
data Cosink (as :: [k]) where
  Cone :: Cone (PR a) (L as) -> Cosink as

-- | Pullbacks are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrows and the type, which we hide behind an existential.
class (CategoryOf k) => HasPullbacks k where
  pullback :: forall (o :: k) a b. a ~> o -> b ~> o -> Cosink [a, b]

instance HasPullbacks () where
  pullback Unit Unit = Cone (Leg Unit (Leg Unit Apex))

instance (HasPullbacks k1, HasPullbacks k2) => HasPullbacks (k1, k2) where
  pullback (l1 :**: l2) (r1 :**: r2) = case (pullback l1 r1, pullback l2 r2) of
    (Cone (Leg f1 (Leg g1 Apex)), Cone (Leg f2 (Leg g2 Apex))) ->
      Cone (Leg (f1 :**: f2) (Leg (g1 :**: g2) Apex))

-- | In a thin category, arrows don't carry information, so pullbacks are just products.
thinPullback :: forall {k} (o :: k) a b. (HasProducts k) => a ~> o -> b ~> o -> Cosink [a, b]
thinPullback l r = l // r // withObProd @k @a @b $ Cone $ Leg (fst @k @a @b) $ Leg (snd @k @a @b) Apex

equalizerDefault :: forall {k} (a :: k) b. (HasPullbacks k, HasProducts k) => a ~> b -> a ~> b -> Cosink '[a]
equalizerDefault f@Objs g = case pullback (obj @a &&& f) (obj @a &&& g) of
  Cone (Leg _ cone) -> Cone cone

kernelDefault :: (HasPullbacks k, HasProducts k, HasZeroObject k) => (a :: k) ~> b -> Cosink '[a]
kernelDefault f@Objs = equalizerDefault zero f

class ik `InternalIn` k where
  type C0 ik :: k
  type C1 ik :: k
  source :: C1 ik ~> (C0 ik :: k)
  target :: C1 ik ~> (C0 ik :: k)
  identity :: C0 ik ~> (C1 ik :: k)
  compose :: Cosink [C1 ik, C1 ik, C1 ik :: k] -- first arrow projection, second arrow projection, composite
