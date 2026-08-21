{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Limit.Equalizer where

import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.Initial (HasZeroObject (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Object (pattern Objs)

-- | Equalizers are an inherently dependently typed concept:
-- The type of the base object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrow and the type, which we hide behind an existential.
class (CategoryOf k) => HasEqualizers k where
  equalize :: forall (a :: k) b r. a ~> b -> a ~> b -> (forall e. e ~> a -> r) -> r

  -- | @factorEqualizer incl h@ requires @incl@ to be mono and @h@'s image to lie within @incl@'s
  -- image; @incl@ is typically (though not necessarily) the equalizer arrow produced by 'equalize'.
  factorEqualizer :: forall (e :: k) x e'. e ~> x -> e' ~> x -> e' ~> e

instance HasEqualizers () where
  equalize Unit Unit k = k Unit
  factorEqualizer Unit Unit = Unit

instance (HasEqualizers k1, HasEqualizers k2) => HasEqualizers (k1, k2) where
  equalize (l1 :**: l2) (r1 :**: r2) k = equalize l1 r1 \f1 -> equalize l2 r2 \f2 -> k (f1 :**: f2)
  factorEqualizer (i1 :**: i2) (h1 :**: h2) = factorEqualizer i1 h1 :**: factorEqualizer i2 h2

-- | In a thin category, arrows don't carry information, so equalizers are just identities.
thinEqualize :: forall {k} (a :: k) b r. (Thin k) => a ~> b -> a ~> b -> (forall e. e ~> a -> r) -> r
thinEqualize Objs _ k = k id

-- | Standalone helper (not a class method) usable as the @default@ implementation of
-- 'Proarrow.Limit.Pullback.pullback' wherever @(HasEqualizers k, HasProducts k)@ happen to hold --
-- not needed by (or required of) every 'Proarrow.Limit.Pullback.HasPullbacks' instance.
pullbackDefault
  :: forall {k} (o :: k) a b r
   . (HasEqualizers k, HasProducts k) => a ~> o -> b ~> o -> (forall p. p ~> a -> p ~> b -> r) -> r
pullbackDefault f@Objs g@Objs k = equalize (f . fst @k @a @b) (g . snd @k @a @b) \e@Objs -> k (fst @k @a @b . e) (snd @k @a @b . e)

-- | Given a pullback's own legs @p1, p2@ and a compatible cone @k1, k2@ on some @q@ (with
-- @f . k1 == g . k2@ for whichever cospan @p1, p2@ are a pullback of), produces the unique
-- @q ~> p@ through which the cone factors. Standalone helper (not a class method), usable as the
-- @default@ implementation of 'Proarrow.Limit.Pullback.factorPullback' wherever
-- @(HasEqualizers k, HasProducts k)@ happen to hold, exactly like 'pullbackDefault' itself.
factorPullbackDefault
  :: forall {k} (a :: k) b p q
   . (HasEqualizers k, HasProducts k)
  => p ~> a -> p ~> b -> q ~> a -> q ~> b -> q ~> p
factorPullbackDefault p1@Objs p2@Objs k1 k2 = factorEqualizer (p1 &&& p2) (k1 &&& k2)

kernel :: (HasEqualizers k, HasZeroObject k) => (a :: k) ~> b -> (forall e. e ~> a -> r) -> r
kernel f@Objs = equalize zero f
