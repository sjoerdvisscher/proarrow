module Proarrow.Limit.Equalizer where

import Proarrow.Category.Enriched.Thin (Thin)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Colimit.Initial (HasInitialObject (..), HasZeroObject (..))
import Proarrow.Core (CategoryOf (..), Hom, Promonad (..))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))

-- | Equalizers are an inherently dependently typed concept:
-- The type of the base object depends on the values of the given arrows.
-- But at runtime we can still calculate the arrow and the type, which we hide behind an existential.
class (CategoryOf k) => HasEqualizers k where
  equalize :: forall (a :: k) b r. a ~> b -> a ~> b -> (forall e. e ~> a -> r) -> r
  default equalize :: forall (a :: k) b r. (HasInitialObject k) => a ~> b -> a ~> b -> (forall e. e ~> a -> r) -> r
  equalize l@Objs r k = case factorEqualizer l r initiate of _ :.: f@Objs -> k f
  factorEqualizer :: forall (a :: k) b c. a ~> b -> a ~> b -> c ~> a -> (Hom k :.: Hom k) c a

instance HasEqualizers () where
  factorEqualizer Unit Unit Unit = Unit :.: Unit

instance (HasEqualizers k1, HasEqualizers k2) => HasEqualizers (k1, k2) where
  equalize (l1 :**: l2) (r1 :**: r2) k = equalize l1 r1 \f1 -> equalize l2 r2 \f2 -> k (f1 :**: f2)
  factorEqualizer (l1 :**: l2) (r1 :**: r2) (f1 :**: f2) = case (factorEqualizer l1 r1 f1, factorEqualizer l2 r2 f2) of
    (l :.: r, f :.: g) -> (l :**: f) :.: (r :**: g)

-- | In a thin category, arrows don't carry information, so equalizers are just identities.
thinEqualize :: forall {k} (a :: k) b r. (Thin k) => a ~> b -> a ~> b -> (forall e. e ~> a -> r) -> r
thinEqualize Objs _ k = k id

thinFactorEqualizer :: forall {k} (a :: k) b c. (Thin k) => a ~> b -> a ~> b -> c ~> a -> (Hom k :.: Hom k) c a
thinFactorEqualizer _ _ f@Objs = id :.: f

pullbackDefault
  :: forall {k} (o :: k) a b r
   . (HasEqualizers k, HasProducts k) => a ~> o -> b ~> o -> (forall p. p ~> a -> p ~> b -> r) -> r
pullbackDefault f@Objs g@Objs k = equalize (f . fst @k @a @b) (g . snd @k @a @b) \e@Objs -> k (fst @k @a @b . e) (snd @k @a @b . e)

kernel :: (HasEqualizers k, HasZeroObject k) => (a :: k) ~> b -> (forall e. e ~> a -> r) -> r
kernel f@Objs = equalize zero f
