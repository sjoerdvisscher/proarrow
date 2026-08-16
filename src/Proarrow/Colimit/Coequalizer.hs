{-# OPTIONS_GHC -Wno-orphans #-}

module Proarrow.Colimit.Coequalizer where

import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Opposite (OPPOSITE, Op (..))
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Initial (HasZeroObject (..))
import Proarrow.Core (CategoryOf (..), Hom, Promonad (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))

-- | Coequalizers are an inherently dependently typed concept:
-- The type of the apex object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrow and the type, which we hide behind an existential.
class (CategoryOf k) => HasCoequalizers k where
  coequalize :: forall (a :: k) b r. a ~> b -> a ~> b -> (forall c. b ~> c -> r) -> r
  default coequalize :: forall (a :: k) b r. (HasTerminalObject k) => a ~> b -> a ~> b -> (forall c. b ~> c -> r) -> r
  coequalize l@Objs r k = case factorCoequalizer l r terminate of f@Objs :.: _ -> k f

  -- | @factorCoequalizer f g h@ requires @h . f == h . g@.
  factorCoequalizer :: forall (a :: k) b c. a ~> b -> a ~> b -> b ~> c -> (Hom k :.: Hom k) b c

instance HasCoequalizers () where
  factorCoequalizer Unit Unit Unit = Unit :.: Unit

instance (HasCoequalizers k1, HasCoequalizers k2) => HasCoequalizers (k1, k2) where
  coequalize (l1 :**: l2) (r1 :**: r2) k = coequalize l1 r1 \f1 -> coequalize l2 r2 \f2 -> k (f1 :**: f2)
  factorCoequalizer (l1 :**: l2) (r1 :**: r2) (f1 :**: f2) = case (factorCoequalizer l1 r1 f1, factorCoequalizer l2 r2 f2) of
    (l :.: r, f :.: g) -> (l :**: f) :.: (r :**: g)

-- | In a thin category, arrows don't carry information, so coequalizers are just coproducts.
thinCoequalize :: forall {k} (a :: k) b r. (Thin k) => a ~> b -> a ~> b -> (forall c. b ~> c -> r) -> r
thinCoequalize Objs _ k = k id

thinFactorCoequalizer :: forall {k} (a :: k) b c. (Thin k) => a ~> b -> a ~> b -> b ~> c -> (Hom k :.: Hom k) b c
thinFactorCoequalizer _ _ f@Objs = f :.: id

pushoutDefault
  :: forall {k} (o :: k) a b r
   . (HasCoequalizers k, HasCoproducts k) => o ~> a -> o ~> b -> (forall p. a ~> p -> b ~> p -> r) -> r
pushoutDefault f@Objs g@Objs k = coequalize (lft @k @a @b . f) (rgt @k @a @b . g) \c@Objs ->
  k (c . lft @k @a @b) (c . rgt @k @a @b)

cokernel :: (HasCoequalizers k, HasZeroObject k) => (a :: k) ~> b -> (forall c. b ~> c -> r) -> r
cokernel f@Objs = coequalize zero f

instance (HasEqualizers k) => HasCoequalizers (OPPOSITE k) where
  coequalize (Op l) (Op r) k = equalize l r (k . Op)
  factorCoequalizer (Op l) (Op r) (Op f) = case factorEqualizer l r f of
    l' :.: r' -> Op r' :.: Op l'

instance (HasCoequalizers k) => HasEqualizers (OPPOSITE k) where
  equalize (Op l) (Op r) k = coequalize l r (k . Op)
  factorEqualizer (Op l) (Op r) (Op f) = case factorCoequalizer l r f of
    l' :.: r' -> Op r' :.: Op l'