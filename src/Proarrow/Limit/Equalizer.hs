module Proarrow.Limit.Equalizer where

import Prelude (($))

import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.Initial (HasZeroObject (..))
import Proarrow.Core (CategoryOf (..), Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Cone (Cone (..), Cosink (..))

-- | Equalizers are an inherently dependently typed concept:
-- The type of the base object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrow and the type, which we hide behind an existential.
class (CategoryOf k) => HasEqualizers k where
  equalize :: forall (a :: k) b. a ~> b -> a ~> b -> Cosink '[a]

instance HasEqualizers () where
  equalize Unit Unit = Cone (Leg Unit Apex)

instance (HasEqualizers k1, HasEqualizers k2) => HasEqualizers (k1, k2) where
  equalize (l1 :**: l2) (r1 :**: r2) = case (equalize l1 r1, equalize l2 r2) of
    (Cone (Leg f1 Apex), Cone (Leg f2 Apex)) ->
      Cone (Leg (f1 :**: f2) Apex)

-- | In a thin category, arrows don't carry information, so equalizers are just identities.
thinEqualize :: forall {k} (a :: k) b. (CategoryOf k) => a ~> b -> a ~> b -> Cosink '[a]
thinEqualize Objs _ = Cone $ Leg id Apex

pullbackDefault :: forall {k} (o :: k) a b. (HasEqualizers k, HasProducts k) => a ~> o -> b ~> o -> Cosink [a, b]
pullbackDefault f@Objs g@Objs = case equalize (f . fst @k @a @b) (g . snd @k @a @b) of
  Cone (Leg e Apex) -> Cone (Leg (fst @k @a @b . e) (Leg (snd @k @a @b . e) Apex))

kernel :: (HasEqualizers k, HasZeroObject k) => (a :: k) ~> b -> Cosink '[a]
kernel f@Objs = equalize zero f
