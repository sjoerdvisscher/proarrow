{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Colimit.Pushout where

import Prelude (Bool, ($), (==))

import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Free (Eq2)
import Proarrow.Category.Instance.Opposite (OPPOSITE, Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Core (CategoryOf (..), Hom, obj, (//))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Object (pattern Objs)

-- | Pushouts are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrows and the type, which we hide behind an existential.
class (CategoryOf k) => HasPushouts k where
  pushout :: forall (o :: k) a b r. o ~> a -> o ~> b -> (forall p. a ~> p -> b ~> p -> r) -> r

instance HasPushouts () where
  pushout Unit Unit k = k Unit Unit

instance (HasPushouts k1, HasPushouts k2) => HasPushouts (k1, k2) where
  pushout (l1 :**: l2) (r1 :**: r2) k = pushout l1 r1 \f1 g1 -> pushout l2 r2 \f2 g2 -> k (f1 :**: f2) (g1 :**: g2)

-- | In a thin category, arrows don't carry information, so pushouts are just coproducts.
thinPushout
  :: forall {k} (o :: k) a b r. (Thin k, HasCoproducts k) => o ~> a -> o ~> b -> (forall p. a ~> p -> b ~> p -> r) -> r
thinPushout l r k = l // r // withObCoprod @k @a @b $ k (lft @k @a @b) (rgt @k @a @b)

coequalizerDefault
  :: forall {k} (a :: k) b r. (HasPushouts k, HasCoproducts k) => a ~> b -> a ~> b -> (forall c. b ~> c -> r) -> r
coequalizerDefault f@Objs g k = pushout (obj @b ||| f) (obj @b ||| g) \_ -> k

cokernelPair :: (HasPushouts k) => (a :: k) ~> b -> (forall p. b ~> p -> b ~> p -> r) -> r
cokernelPair f = pushout f f

isEpi :: (HasPushouts k, Eq2 (Hom k)) => (a :: k) ~> b -> Bool
isEpi f@Objs = cokernelPair f \l@Objs r -> l == r

instance (HasPullbacks k) => HasPushouts (OPPOSITE k) where
  pushout (Op l) (Op r) k = pullback l r \f g -> k (Op f) (Op g)

instance (HasPushouts k) => HasPullbacks (OPPOSITE k) where
  pullback (Op l) (Op r) k = pushout l r \f g -> k (Op f) (Op g)