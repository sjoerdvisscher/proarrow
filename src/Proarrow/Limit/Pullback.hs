{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Limit.Pullback where

import Prelude (Bool, const, ($), (==))

import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Free (Eq2)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CategoryOf (..), Hom, obj, (//))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Limit.Equalizer (HasEqualizers, factorPullbackDefault, pullbackDefault)
import Proarrow.Object (pattern Objs)

-- | Pullbacks are an inherently dependently typed concept:
-- The type of the base object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrows and the type, which we hide behind an existential.
class (CategoryOf k) => HasPullbacks k where
  pullback :: forall (o :: k) a b r. a ~> o -> b ~> o -> (forall p. p ~> a -> p ~> b -> r) -> r
  default pullback
    :: forall (o :: k) a b r
     . (HasEqualizers k, HasProducts k)
    => a ~> o -> b ~> o -> (forall p. p ~> a -> p ~> b -> r) -> r
  pullback = pullbackDefault

  -- | @factorPullback p1 p2 k1 k2@ requires @k1, k2@ to be a compatible cone for whichever cospan
  -- @p1, p2@ happen to be a pullback of -- @p1, p2@ need not literally be @pullback@'s own output.
  factorPullback :: forall (a :: k) b p q. p ~> a -> p ~> b -> q ~> a -> q ~> b -> q ~> p
  default factorPullback
    :: forall (a :: k) b p q. (HasEqualizers k, HasProducts k) => p ~> a -> p ~> b -> q ~> a -> q ~> b -> q ~> p
  factorPullback = factorPullbackDefault

instance HasPullbacks () where
  pullback Unit Unit k = k Unit Unit
  factorPullback Unit Unit Unit Unit = Unit

instance (HasPullbacks k1, HasPullbacks k2) => HasPullbacks (k1, k2) where
  pullback (l1 :**: l2) (r1 :**: r2) k = pullback l1 r1 \f1 g1 -> pullback l2 r2 \f2 g2 -> k (f1 :**: f2) (g1 :**: g2)
  factorPullback (p1a :**: p1b) (p2a :**: p2b) (k1a :**: k1b) (k2a :**: k2b) =
    factorPullback p1a p2a k1a k2a :**: factorPullback p1b p2b k1b k2b

-- | In a thin category, arrows don't carry information, so pullbacks are just products.
thinPullback
  :: forall {k} (o :: k) a b r. (Thin k, HasProducts k) => a ~> o -> b ~> o -> (forall p. p ~> a -> p ~> b -> r) -> r
thinPullback l r k = l // r // withObProd @k @a @b $ k (fst @k @a @b) (snd @k @a @b)

equalizerDefault
  :: forall {k} (a :: k) b r. (HasPullbacks k, HasProducts k) => a ~> b -> a ~> b -> (forall e. e ~> a -> r) -> r
equalizerDefault f@Objs g k = pullback (obj @a &&& f) (obj @a &&& g) (const k)

kernelPair :: (HasPullbacks k) => (a :: k) ~> b -> (forall p. p ~> a -> p ~> a -> r) -> r
kernelPair f = pullback f f

isMono :: (HasPullbacks k, Eq2 (Hom k)) => (a :: k) ~> b -> Bool
isMono f = kernelPair f \l@Objs r -> l == r
