module Proarrow.Category.Instance.Coproduct where

import Data.Kind (Constraint)
import Prelude (type (~))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Topos (HasEpiMonoFactorization (..), defaultFactorize)
import Proarrow.Colimit.Coequalizer (HasCoequalizers (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Limit.Equalizer (HasEqualizers (..))
import Proarrow.Limit.Pullback (HasPullbacks (..))
import Proarrow.Profunctor.Corepresentable (Corepresentable (..))
import Proarrow.Profunctor.Representable (Representable (..))

type data COPRODUCT j k = L j | R k

type (:++:) :: (j1 +-> k1) -> (j2 +-> k2) -> COPRODUCT j1 j2 +-> COPRODUCT k1 k2
data (:++:) p q a b where
  InjL :: p a b -> (p :++: q) (L a) (L b)
  InjR :: q a b -> (p :++: q) (R a) (R b)

type IsLR :: forall {j} {k}. COPRODUCT j k -> Constraint
class IsLR (a :: COPRODUCT j k) where
  lrCase :: (forall b. (a ~ L b, Ob b) => r) -> (forall b. (a ~ R b, Ob b) => r) -> r
instance (Ob a) => IsLR (L a :: COPRODUCT j k) where
  lrCase l _ = l
instance (Ob a) => IsLR (R a :: COPRODUCT j k) where
  lrCase _ r = r

instance (Profunctor p, Profunctor q) => Profunctor (p :++: q) where
  dimap (InjL f) (InjL g) (InjL p) = InjL (dimap f g p)
  dimap (InjR f) (InjR g) (InjR q) = InjR (dimap f g q)
  dimap InjL{} InjR{} p = case p of {}
  dimap InjR{} InjL{} q = case q of {}
  r \\ InjL p = r \\ p
  r \\ InjR q = r \\ q

-- | The coproduct of two promonads.
instance (Promonad p, Promonad q) => Promonad (p :++: q) where
  id @a = lrCase @a (InjL id) (InjR id)
  InjL p . InjL q = InjL (p . q)
  InjR q . InjR r = InjR (q . r)

-- | The coproduct of two categories.
instance (CategoryOf j, CategoryOf k) => CategoryOf (COPRODUCT j k) where
  type (~>) @(COPRODUCT j k) = (~>) @j :++: (~>) @k
  type Ob (a :: COPRODUCT j k) = IsLR a

instance (Representable p, Representable q) => Representable (p :++: q) where
  type (p :++: q) % L a = L (p % a)
  type (p :++: q) % R a = R (q % a)
  index (InjL p) = InjL (index p)
  index (InjR q) = InjR (index q)
  repUniv @a = lrCase @a (InjL (repUniv @p)) (InjR (repUniv @q))

instance (Corepresentable p, Corepresentable q) => Corepresentable (p :++: q) where
  type (p :++: q) %% L a = L (p %% a)
  type (p :++: q) %% R a = R (q %% a)
  coindex (InjL f) = InjL (coindex f)
  coindex (InjR f) = InjR (coindex f)
  corepUniv @a = lrCase @a (InjL (corepUniv @p)) (InjR (corepUniv @q))

instance (DaggerProfunctor p, DaggerProfunctor q) => DaggerProfunctor (p :++: q) where
  dagger = \case
    InjL f -> InjL (dagger f)
    InjR f -> InjR (dagger f)

-- | Morphisms of 'COPRODUCT' never cross sides, so this is a straight case split reusing @j@'s or
-- @k@'s own equalizer -- never a mix of the two.
instance (HasEqualizers j, HasEqualizers k) => HasEqualizers (COPRODUCT j k) where
  equalize (InjL f) (InjL g) k = equalize f g \e -> k (InjL e)
  equalize (InjR f) (InjR g) k = equalize f g \e -> k (InjR e)
  factorEqualizer (InjL incl) (InjL h) = InjL (factorEqualizer incl h)
  factorEqualizer (InjR incl) (InjR h) = InjR (factorEqualizer incl h)

-- | Dual to the 'HasEqualizers' instance above.
instance (HasCoequalizers j, HasCoequalizers k) => HasCoequalizers (COPRODUCT j k) where
  coequalize (InjL f) (InjL g) k = coequalize f g \c -> k (InjL c)
  coequalize (InjR f) (InjR g) k = coequalize f g \c -> k (InjR c)
  factorCoequalizer (InjL q) (InjL h) = InjL (factorCoequalizer q h)
  factorCoequalizer (InjR q) (InjR h) = InjR (factorCoequalizer q h)

instance (HasPullbacks j, HasPullbacks k) => HasPullbacks (COPRODUCT j k) where
  pullback (InjL f) (InjL g) k = pullback f g \p1 p2 -> k (InjL p1) (InjL p2)
  pullback (InjR f) (InjR g) k = pullback f g \p1 p2 -> k (InjR p1) (InjR p2)
  factorPullback (InjL p1) (InjL p2) (InjL k1) (InjL k2) = InjL (factorPullback p1 p2 k1 k2)
  factorPullback (InjR p1) (InjR p2) (InjR k1) (InjR k2) = InjR (factorPullback p1 p2 k1 k2)

instance (HasPushouts j, HasPushouts k) => HasPushouts (COPRODUCT j k) where
  pushout (InjL f) (InjL g) k = pushout f g \p1 p2 -> k (InjL p1) (InjL p2)
  pushout (InjR f) (InjR g) k = pushout f g \p1 p2 -> k (InjR p1) (InjR p2)
  factorPushout (InjL p1) (InjL p2) (InjL k1) (InjL k2) = InjL (factorPushout p1 p2 k1 k2)
  factorPushout (InjR p1) (InjR p2) (InjR k1) (InjR k2) = InjR (factorPushout p1 p2 k1 k2)

instance (HasPushouts j, HasEqualizers j, HasPushouts k, HasEqualizers k) => HasEpiMonoFactorization (COPRODUCT j k) where
  factorize = defaultFactorize

data family Lft :: j +-> COPRODUCT j k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (Lft :: j +-> COPRODUCT j k) where
  type Lft @ a = L a
  fmap = InjL

data family Rgt :: k +-> COPRODUCT j k
instance (CategoryOf j, CategoryOf k) => FunctorForRep (Rgt :: k +-> COPRODUCT j k) where
  type Rgt @ a = R a
  fmap = InjR

data family Codiag :: COPRODUCT k k +-> k
instance (CategoryOf k) => FunctorForRep (Codiag :: COPRODUCT k k +-> k) where
  type Codiag @ L a = a
  type Codiag @ R a = a
  fmap = \case
    InjL f -> f
    InjR g -> g
