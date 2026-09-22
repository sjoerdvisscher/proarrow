-- | __Sieves__: a @'Sieve' a b@ says which arrows into @a@ and out of @b@ are in. Being /in/ has to
-- survive composing on either side: if @g@ and @h@ are in, so are @g '.' l@ and @r '.' h@ for any
-- @l@ and @r@. That closure is what makes a sieve a sieve.
--
-- __The constructor does not check it.__ It takes any predicate at all, so it will build a value
-- that is not a sieve. Where checking is cheap the closure is checked rather than trusted:
-- 'Proarrow.Category.Enriched.Finitary.Finitary'\'s @toIndex@ fails with @\"not a sieve\"@, and
-- 'Proarrow.Category.Enriched.Finitary.Topos.withSubobject' takes its failure branch. Elsewhere it
-- is presupposed -- 'Proarrow.Category.Enriched.Finitary.Sheaf.coveringCover' reads a cover's legs
-- and concludes about everything they generate -- so on a value that is not a sieve those two kinds
-- of function part company. If you construct a 'Sieve' by hand, the closure is yours to get right.
--
-- Sieves are the subobjects of the representable at @a@\/@b@, so they are the truth values of a
-- category of profunctors, and "Proarrow.Category.Enriched.Finitary.Topos" makes them the
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
-- profunctors; this is the one value @yes@, which is why it is the
-- 'Proarrow.Category.Topos.true' of their subobject classifier. A sieve is called /dense/ for a
-- coverage when its closure is this one -- see
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.closure'.
maximalSieve :: forall {j} {k} (a :: k) (b :: j). (CategoryOf j, CategoryOf k, Ob a, Ob b) => Sieve a b
maximalSieve = Sieve \_ _ -> True

-- | The sieve of arrows in both -- the @and@ of the truth values the two stand for, which is
-- 'Proarrow.Category.Topos.and' at the classifier of
-- "Proarrow.Category.Enriched.Finitary.Topos", computed directly rather than as an arrow. Being
-- closed under composition is pointwise, so the meet of two sieves is again one; the meet of all
-- the /dense/ sieves at a pair of objects is what
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.Plus' is computed on.
sieveMeet :: Sieve a b -> Sieve a b -> Sieve a b
sieveMeet (Sieve s) (Sieve s') = Sieve \g h -> s g h && s' g h
