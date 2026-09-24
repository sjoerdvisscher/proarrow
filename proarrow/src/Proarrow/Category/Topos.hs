{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Elementary toposes: 'HasSubobjectClassifier' provides the object 'Omega' of truth values
-- classifying monomorphisms, 'HasEpiMonoFactorization' the image factorization, and
-- 'ElementaryTopos' combines these with finite (co)limits and exponentials, yielding the internal
-- logic ('false', 'and', 'or', 'implies').
module Proarrow.Category.Topos where

import Proarrow.Category.Monoidal.Cartesian (CCC)
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasCoproducts)
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..), cokernelPair)
import Proarrow.Core (CategoryOf (..), Hom, Promonad (..), obj)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), HasProducts, PROD, Prod (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..), const)
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
  -- | Factor an arrow as an epi followed by a mono. Defaults to 'defaultFactorize', the image
  -- factorization via the cokernel pair, which applies whenever @k@ has pushouts and equalizers.
  factorize :: (a ~> b) -> (Hom k :.: Hom k) a b
  default factorize :: (HasPushouts k, HasEqualizers k) => (a ~> b) -> (Hom k :.: Hom k) a b
  factorize = defaultFactorize

defaultFactorize :: (HasPushouts k, HasEqualizers k) => (a ~> b) -> (Hom k :.: Hom k) a b
defaultFactorize f = pushout f f \q1 q2 -> equalize q1 q2 \incl -> factorEqualizer incl f :.: incl

defaultFactorizeDual :: (HasPullbacks k, HasCoequalizers k) => a ~> b -> (Hom k :.: Hom k) a b
defaultFactorizeDual f = pullback f f \p1 p2 -> coequalize p1 p2 \incl -> incl :.: factorCoequalizer incl f

-- | Image factorization is unchanged by making the tensor the product.
instance (HasEpiMonoFactorization k) => HasEpiMonoFactorization (PROD k) where
  factorize (Prod f) = case factorize f of e :.: m -> Prod e :.: Prod m

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
or = classifyImage (const @Omega true &&& id ||| id &&& const @Omega true)

implies :: forall k. (ElementaryTopos k) => (Omega :: k) && Omega ~> Omega
implies = equalize and (fst @k @Omega @Omega) classifyImage

-- | Negation: the classifying map of 'false', which is a mono as every arrow out of the terminal
-- object is. The same arrow as @u ⇒ false@.
not :: forall k. (ElementaryTopos k) => (Omega :: k) ~> Omega
-- Not through 'implies', which classifies a subobject of @Omega && Omega@ where this classifies
-- one of 'Omega', and 'classifyImage' squares the cokernel pair of whatever it is given.
not = classifyImage (false @k)

-- * Lawvere–Tierney topologies

-- $topologies
-- A Lawvere–Tierney topology is an arrow @j :: 'Omega' '~>' 'Omega'@ that fixes 'true', is
-- idempotent and preserves 'and'. Its sheaves form a subtopos. Every topos has the two extremes,
-- 'id' (every object a sheaf) and @'const' 'true'@ (only the terminal one), and the internal
-- logic gives the ones below. A coverage gives another, by closing sieves:
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.lawvereTierney'.
-- @Proarrow.Testing.Laws.testLawvereTierney@ checks the three laws.

-- | The double-negation topology @¬¬@, whose sheaves form the smallest dense subtopos, and a
-- Boolean one. On a presheaf topos it is the dense topology: a sieve on @a@ covers when every arrow
-- into @a@ can be extended to one in the sieve. When every cospan can be completed to a commuting
-- square (the Ore condition, which pullbacks provide), that is the atomic topology, so there
-- 'Proarrow.Category.Sheaf.Atomic' computes this by closing sieves. In a Boolean topos it is 'id'.
doubleNegation :: forall k. (ElementaryTopos k) => (Omega :: k) ~> Omega
doubleNegation = not @k . not @k

-- | The open topology of a truth value @u@: @u ⇒ -@. Its sheaves are the open subtopos of the
-- subterminal object @u@ classifies, the part of the topos lying over @u@. @'openTopology' 'true'@
-- is 'id' and @'openTopology' 'false'@ is @'const' 'true'@.
openTopology :: forall k. (ElementaryTopos k) => TerminalObject ~> (Omega :: k) -> (Omega :: k) ~> Omega
-- A lambda under the binding, so that 'implies' is built once and shared by every @u@. It is an
-- image to classify, and a family of topologies is typically used at many truth values.
openTopology = \u -> i . (const u &&& id)
  where
    i = implies @k

-- | The closed topology of a truth value @u@: @u ∨ -@, complementary to 'openTopology'. Its
-- sheaves are the part of the topos lying away from @u@. @'closedTopology' 'true'@ is
-- @'const' 'true'@ and @'closedTopology' 'false'@ is 'id'.
closedTopology :: forall k. (ElementaryTopos k) => TerminalObject ~> (Omega :: k) -> (Omega :: k) ~> Omega
-- A lambda under the binding, so that 'or' is built once and shared, as in 'openTopology'.
closedTopology = \u -> o . (const u &&& id)
  where
    o = or @k
