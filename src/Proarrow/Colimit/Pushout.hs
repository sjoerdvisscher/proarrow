{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Colimit.Pushout where

import Prelude (($))

import Proarrow.Category.Instance.Opposite (OPPOSITE, Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Core (CategoryOf (..), obj, (//))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Cocone (Cocone (..), Sink (..))
import Proarrow.Profunctor.Instance.Cone (Cone (..), Cosink (..))

-- | Pushouts are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrows and the type, which we hide behind an existential.
class (CategoryOf k) => HasPushouts k where
  pushout :: forall (o :: k) a b. o ~> a -> o ~> b -> Sink [a, b]

instance HasPushouts () where
  pushout Unit Unit = Cocone (Coleg Unit (Coleg Unit Coapex))

instance (HasPushouts k1, HasPushouts k2) => HasPushouts (k1, k2) where
  pushout (l1 :**: l2) (r1 :**: r2) = case (pushout l1 r1, pushout l2 r2) of
    (Cocone (Coleg f1 (Coleg g1 Coapex)), Cocone (Coleg f2 (Coleg g2 Coapex))) ->
      Cocone (Coleg (f1 :**: f2) (Coleg (g1 :**: g2) Coapex))

-- | In a thin category, arrows don't carry information, so pushouts are just coproducts.
thinPushout :: forall {k} (o :: k) a b. (HasCoproducts k) => o ~> a -> o ~> b -> Sink [a, b]
thinPushout l r = l // r // withObCoprod @k @a @b $ Cocone $ Coleg (lft @k @a @b) $ Coleg (rgt @k @a @b) Coapex

coequalizerDefault :: forall {k} (a :: k) b. (HasPushouts k, HasCoproducts k) => a ~> b -> a ~> b -> Sink '[b]
coequalizerDefault f@Objs g = case pushout (obj @b ||| f) (obj @b ||| g) of
  Cocone (Coleg _ cocone) -> Cocone cocone

instance (HasPullbacks k) => HasPushouts (OPPOSITE k) where
  pushout (Op l) (Op r) = case pullback l r of Cone (Leg f (Leg g Apex)) -> Cocone (Coleg (Op f) (Coleg (Op g) Coapex))

instance (HasPushouts k) => HasPullbacks (OPPOSITE k) where
  pullback (Op l) (Op r) = case pushout l r of Cocone (Coleg f (Coleg g Coapex)) -> Cone (Leg (Op f) (Leg (Op g) Apex))