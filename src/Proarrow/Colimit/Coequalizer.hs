{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Colimit.Coequalizer where

import Prelude (($))

import Proarrow.Category.Instance.Opposite (OPPOSITE, Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Initial (HasZeroObject (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Cocone (Cocone (..), Sink (..))
import Proarrow.Profunctor.Instance.Cone (Cone (..), Cosink (..))

-- | Coequalizers are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrow and the type, which we hide behind an existential.
class (CategoryOf k) => HasCoequalizers k where
  coequalize :: forall (a :: k) b. a ~> b -> a ~> b -> Sink '[b]

instance HasCoequalizers () where
  coequalize Unit Unit = Cocone (Coleg Unit Coapex)

instance (HasCoequalizers k1, HasCoequalizers k2) => HasCoequalizers (k1, k2) where
  coequalize (l1 :**: l2) (r1 :**: r2) = case (coequalize l1 r1, coequalize l2 r2) of
    (Cocone (Coleg f1 Coapex), Cocone (Coleg f2 Coapex)) ->
      Cocone (Coleg (f1 :**: f2) Coapex)

-- | In a thin category, arrows don't carry information, so coequalizers are just coproducts.
thinCoequalize :: forall {k} (a :: k) b. (CategoryOf k) => a ~> b -> a ~> b -> Sink '[b]
thinCoequalize Objs _ = Cocone $ Coleg id Coapex

pushoutDefault :: forall {k} (o :: k) a b. (HasCoequalizers k, HasCoproducts k) => o ~> a -> o ~> b -> Sink [a, b]
pushoutDefault f@Objs g@Objs = case coequalize (lft @k @a @b . f) (rgt @k @a @b . g) of
  Cocone (Coleg c Coapex) -> Cocone (Coleg (c . lft @k @a @b) (Coleg (c . rgt @k @a @b) Coapex))

cokernel :: (HasCoequalizers k, HasZeroObject k) => (a :: k) ~> b -> Sink '[b]
cokernel f@Objs = coequalize zero f

instance (HasEqualizers k) => HasCoequalizers (OPPOSITE k) where
  coequalize (Op l) (Op r) = case equalize l r of Cone (Leg f Apex) -> Cocone (Coleg (Op f) Coapex)

instance (HasCoequalizers k) => HasEqualizers (OPPOSITE k) where
  equalize (Op l) (Op r) = case coequalize l r of Cocone (Coleg f Coapex) -> Cone (Leg (Op f) Apex)