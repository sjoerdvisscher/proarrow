{-# LANGUAGE AllowAmbiguousTypes #-}

module Proarrow.Category.Topos where

import Proarrow.Category.Monoidal.Closed (CCC)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..), cokernelPair)
import Proarrow.Core (CategoryOf (..), Hom, Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts)
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))

class (HasProducts k, Ob (Omega :: k)) => HasSubobjectClassifier k where
  type Omega :: k
  true :: TerminalObject ~> (Omega :: k)
  default true :: (HasProducts k, HasPushouts k) => TerminalObject ~> (Omega :: k)
  true = classifyImage (obj @TerminalObject)

  -- | Classify the graph (@id *** f :: a ~> a && b@) of a morphism @f@.
  -- This is a minimal primitive that works for any morphism.
  classifyGraph :: a ~> b -> a && b ~> (Omega :: k)

isEq :: forall {k} (a :: k). (HasSubobjectClassifier k, Ob a) => a && a ~> Omega
isEq = classifyGraph (obj @a)

-- | @classify f@ classifies the image of @f@. If @f@ is mono, then this returns its characteristic map.
classifyImage :: forall {k} (a :: k) b. (HasSubobjectClassifier k, HasPushouts k) => a ~> b -> b ~> Omega
classifyImage f = cokernelPair f \ @im g1@Objs g2 -> isEq @im . (g1 &&& g2)

classifyKernelPair :: forall {k} (a :: k) b. (HasSubobjectClassifier k) => a ~> b -> (a && a) ~> Omega
classifyKernelPair f@Objs = isEq @b . (f *** f)

class (CategoryOf k) => HasEpiMonoFactorization k where
  factorize :: (a ~> b) -> (Hom k :.: Hom k) a b

defaultFactorize :: (HasPushouts k, HasEqualizers k) => (a ~> b) -> (Hom k :.: Hom k) a b
defaultFactorize f = pushout f f \q1 q2 -> equalize q1 q2 \incl -> factorEqualizer incl f :.: incl

defaultFactorizeDual :: (HasPullbacks k, HasCoequalizers k) => a ~> b -> (Hom k :.: Hom k) a b
defaultFactorizeDual f = pullback f f \p1 p2 -> coequalize p1 p2 \incl -> incl :.: factorCoequalizer incl f

type HasFiniteLimits k = (HasProducts k, HasPullbacks k, HasEqualizers k)
type HasFiniteColimits k = (HasCoproducts k, HasPushouts k, HasCoequalizers k)

class
  (HasFiniteLimits k, HasFiniteColimits k, CCC k, HasSubobjectClassifier k, HasEpiMonoFactorization k) =>
  ElementaryTopos k

false :: (ElementaryTopos k) => TerminalObject ~> (Omega :: k)
false = classifyImage initiate

and :: forall k. (ElementaryTopos k) => (Omega :: k) && Omega ~> Omega
and = classifyImage (true &&& true)

or :: forall k. (ElementaryTopos k) => (Omega :: k) && Omega ~> Omega
or = classifyImage (constTrue &&& id ||| id &&& constTrue)
  where
    constTrue = true . terminate @k @Omega

implies :: forall k. (ElementaryTopos k) => (Omega :: k) && Omega ~> Omega
implies = equalize and (fst @k @Omega @Omega) classifyImage
