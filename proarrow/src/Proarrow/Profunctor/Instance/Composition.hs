-- | Profunctor composition ':.:', the coend @exists b. (p a b, q b c)@ with the coend hidden in the
-- existential of the constructor. This is the horizontal composition of profunctors; 'Promonad's are the
-- monoids with respect to it.
module Proarrow.Profunctor.Instance.Composition where

import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Core (Profunctor (..), Promonad (..), lmap, rmap, (:~>), type (+->))
import Proarrow.Functor (Functor (..), FunctorForRep (..))

type (:.:) :: (j +-> k) -> (i +-> j) -> (i +-> k)
data (p :.: q) a c where
  (:.:) :: forall b a c p q. ~(p a b) -> ~(q b c) -> (p :.: q) a c

instance (Profunctor p, Profunctor q) => Profunctor (p :.: q) where
  dimap l r (p :.: q) = lmap l p :.: rmap r q
  r \\ p :.: q = r \\ p \\ q

instance (Profunctor p) => Functor ((:.:) p) where
  map (Prof n) = Prof \(p :.: q) -> p :.: n q

instance (FunctorForRep p, FunctorForRep q) => FunctorForRep (p :.: q) where
  type (p :.: q) @ b = p @ (q @ b)
  fmap = fmap @p . fmap @q

-- The 'Proarrow.Category.Enriched.Thin.ThinProfunctor' instance for composition lives in
-- "Proarrow.Category.Enriched.Thin.Composition": in general it needs an existential over the
-- middle objects, which constraints can't express directly, so it either substitutes a
-- representable leg or, when both legs are decidable and the middle category enumerable,
-- searches the middle objects at the type level.

-- | Horizontal composition
o
  :: forall {i} {j} {k} (p :: j +-> k) (q :: j +-> k) (r :: i +-> j) (s :: i +-> j)
   . p :~> q
  -> r :~> s
  -> p :.: r :~> q :.: s
pq `o` rs = \(p :.: r) -> pq p :.: rs r

-- | @p :.: q@ is a `Promonad` if @p@ and @q@ are and if there's a distributive law between @p@ and @q@.
compComp :: (Promonad p, Promonad q) => q :.: p :~> p :.: q -> (p :.: q) b c -> (p :.: q) a b -> (p :.: q) a c
compComp dist (p1 :.: q1) (p2 :.: q2) = case dist (q2 :.: p1) of p3 :.: q3 -> (p3 . p2) :.: (q1 . q3)
