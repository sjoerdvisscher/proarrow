-- | __Sieves__: a @'Sieve' a b@ says which arrows into @a@ and out of @b@ are in, closed under
-- composition on both sides. Sieves are the subobjects of the representable at @a@\/@b@, so they are
-- the truth values of a category of profunctors, and
-- "Proarrow.Category.Enriched.Finitary" makes them the
-- 'Proarrow.Category.Topos.HasSubobjectClassifier' of the finitary ones.
module Proarrow.Profunctor.Instance.Sieve where

import Prelude (Bool)

import Proarrow.Core (CategoryOf (..), Profunctor (..), Promonad (..), (//), type (+->))

type Sieve :: forall {j} {k}. j +-> k
data Sieve a b where
  Sieve :: (Ob a, Ob b) => (forall c d. c ~> a -> b ~> d -> Bool) -> Sieve a b

instance (CategoryOf j, CategoryOf k) => Profunctor (Sieve :: j +-> k) where
  dimap l r (Sieve s) = l // r // Sieve \g h -> s (l . g) (h . r)
  r \\ Sieve{} = r
