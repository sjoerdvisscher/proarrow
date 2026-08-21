{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Colimit.Coequalizer where

import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Opposite (OPPOSITE, Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Initial (HasZeroObject (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Object (pattern Objs)

-- | Coequalizers are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrow and the type, which we hide behind an existential.
class (CategoryOf k) => HasCoequalizers k where
  coequalize :: forall (a :: k) b r. a ~> b -> a ~> b -> (forall c. b ~> c -> r) -> r

  -- | @factorCoequalizer q h@ requires @q@ to be epi and @h@ to be constant on @q@'s fibers; @q@ is
  -- typically (though not necessarily) the coequalizer arrow produced by 'coequalize'.
  factorCoequalizer :: forall (c :: k) x c'. x ~> c -> x ~> c' -> c ~> c'

instance HasCoequalizers () where
  coequalize Unit Unit k = k Unit
  factorCoequalizer Unit Unit = Unit

instance (HasCoequalizers k1, HasCoequalizers k2) => HasCoequalizers (k1, k2) where
  coequalize (l1 :**: l2) (r1 :**: r2) k = coequalize l1 r1 \f1 -> coequalize l2 r2 \f2 -> k (f1 :**: f2)
  factorCoequalizer (q1 :**: q2) (h1 :**: h2) = factorCoequalizer q1 h1 :**: factorCoequalizer q2 h2

-- | In a thin category, arrows don't carry information, so coequalizers are just coproducts.
thinCoequalize :: forall {k} (a :: k) b r. (Thin k) => a ~> b -> a ~> b -> (forall c. b ~> c -> r) -> r
thinCoequalize Objs _ k = k id

-- | Standalone helper (not a class method) usable as the @default@ implementation of
-- 'Proarrow.Colimit.Pushout.pushout' wherever @(HasCoequalizers k, HasCoproducts k)@ happen to hold --
-- not needed by (or required of) every 'Proarrow.Colimit.Pushout.HasPushouts' instance.
pushoutDefault
  :: forall {k} (o :: k) a b r
   . (HasCoequalizers k, HasCoproducts k) => o ~> a -> o ~> b -> (forall p. a ~> p -> b ~> p -> r) -> r
pushoutDefault f@Objs g@Objs k = coequalize (lft @k @a @b . f) (rgt @k @a @b . g) \c@Objs ->
  k (c . lft @k @a @b) (c . rgt @k @a @b)

-- | Given a pushout's own legs @p1, p2@ and a compatible cocone @k1, k2@ out of some @q@ (with
-- @k1 . f == k2 . g@ for whichever cospan @p1, p2@ are a pushout of), produces the unique @p ~> q@
-- through which the cocone factors. Standalone helper (not a class method), usable as the
-- @default@ implementation of 'Proarrow.Colimit.Pushout.factorPushout', dual to
-- 'Proarrow.Limit.Equalizer.factorPullbackDefault'.
factorPushoutDefault
  :: forall {k} (a :: k) b p q
   . (HasCoequalizers k, HasCoproducts k)
  => a ~> p -> b ~> p -> a ~> q -> b ~> q -> p ~> q
factorPushoutDefault p1@Objs p2@Objs k1 k2 = factorCoequalizer (p1 ||| p2) (k1 ||| k2)

cokernel :: (HasCoequalizers k, HasZeroObject k) => (a :: k) ~> b -> (forall c. b ~> c -> r) -> r
cokernel f@Objs = coequalize zero f

instance (HasEqualizers k) => HasCoequalizers (OPPOSITE k) where
  coequalize (Op l) (Op r) k = equalize l r (k . Op)
  factorCoequalizer (Op x1) (Op x2) = Op (factorEqualizer x1 x2)

instance (HasCoequalizers k) => HasEqualizers (OPPOSITE k) where
  equalize (Op l) (Op r) k = coequalize l r (k . Op)
  factorEqualizer (Op x1) (Op x2) = Op (factorCoequalizer x1 x2)
