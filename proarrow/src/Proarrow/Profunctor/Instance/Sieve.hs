-- | __Sieves__: a @'Sieve' a b@ is a set of pairs @(g :: c '~>' a, h :: b '~>' d)@, given as a
-- predicate, that is closed under composing on the outside: if @(g, h)@ is in, so is
-- @(g '.' l, r '.' h)@ for any @l@ and @r@. With @b@ ignored this is the textbook sieve on @a@, a
-- set of arrows into @a@ closed under precomposition.
--
-- __The constructor does not check this closure.__ @toIndex@ of
-- 'Proarrow.Category.Enriched.Finitary.Finitary' (failing with @\"not a sieve\"@) and
-- 'Proarrow.Category.Enriched.Finitary.Topos.withSubobject' check it. Others presuppose it, e.g.
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.coveringCover' judges a sieve by a cover's legs, so
-- on a non-sieve the two kinds of function disagree. A hand-built 'Sieve' must be closed.
--
-- Sieves are the subobjects of the representable at @a@\/@b@, so they are the truth values of a
-- category of profunctors: "Proarrow.Category.Enriched.Finitary.Topos" makes them the
-- 'Proarrow.Category.Topos.HasSubobjectClassifier' of the finitary ones.
module Proarrow.Profunctor.Instance.Sieve where

import Prelude (Bool (..), (&&))

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (//), type (+->))

type Sieve :: forall {j} {k}. j +-> k
data Sieve a b where
  Sieve :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> Bool) -> Sieve a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Sieve :: j +-> k) where
  dimap l r (Sieve s) = l // r // Sieve \g h -> s (l . g) (h . r)
  r \\ Sieve{} = r

-- | The sieve that contains every arrow. 'Sieve' is the /object/ of truth values of a category of
-- profunctors, and this is its value @yes@, so it is the 'Proarrow.Category.Topos.true' of their
-- subobject classifier. A sieve is called /dense/ for a coverage when its closure is this one (see
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.closure').
maximalSieve :: forall {j} {k} (a :: k) (b :: j). (CategoryOf j, CategoryOf k, Ob a, Ob b) => Sieve a b
maximalSieve = Sieve \_ _ -> True

-- | The sieve of arrows in both: the @and@ of the truth values the two stand for. This is
-- 'Proarrow.Category.Topos.and' at the classifier of
-- "Proarrow.Category.Enriched.Finitary.Topos", computed directly instead of as an arrow. Being
-- closed under composition is pointwise, so the meet of two sieves is again one.
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.Plus' is computed on the meet of all the /dense/
-- sieves at a pair of objects.
sieveMeet :: Sieve a b -> Sieve a b -> Sieve a b
sieveMeet (Sieve s) (Sieve s') = Sieve \g h -> s g h && s' g h
