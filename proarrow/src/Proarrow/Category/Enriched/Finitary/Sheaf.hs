{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Sheaves on a finite site, decided by enumeration.
--
-- A cover of @a@ generates a 'Sieve' ('generatedSieve'), and a matching family for that cover is
-- exactly a natural transformation out of the sieve -- which over finitary profunctors is a finite
-- thing you can list. So the sheaf condition becomes a comparison of two finite lists ('sheafAt'):
-- restrict each element at @a@ to get one table per element, enumerate the matching families to get
-- the other list, and check the two agree as multisets. Comparing only their /lengths/ is not
-- enough: @Props.Sheaf@'s @Collapse@ has as many elements as matching families and is still not a
-- sheaf.
--
-- The same coverage is a Lawvere–Tierney topology on the topos. 'closure' sends a sieve to the pairs
-- @(g, h)@ along which it pulls back to a covering one, and 'lawvereTierney' packages that as an
-- arrow on 'Omega'.
module Proarrow.Category.Enriched.Finitary.Sheaf where

import Data.List (sort)
import Prelude qualified as P

import Proarrow.Category.Enriched.Finitary (Finitary (..), FiniteCat, factorsThrough, foreachOb)
import Proarrow.Category.Enriched.Finitary.Topos (FINITARY, natElements, natTable, sieveTable, withSubobject)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..))
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Category.Sheaf (HasFiniteCovers (..), Site (..), SomeCover (..), SomeLeg (..))
import Proarrow.Category.Topos (HasSubobjectClassifier (..))
import Proarrow.Core (CategoryOf (..), Profunctor (..), (\\), type (+->))
import Proarrow.Limit.BinaryProduct (PROD (..), Prod (..))
import Proarrow.Profunctor.Instance.Sieve (Sieve (..))
import Proarrow.Profunctor.Instance.Yoneda (Yo (..))

-- | The sieve a cover generates at @(a, b)@: the arrows into @a@ that factor through a leg,
-- paired with every arrow out of @b@.
generatedSieve
  :: forall t {j} {k} (a :: k) (b :: j) c
   . (Site t k, FiniteCat k, CategoryOf j, Ob a, Ob b)
  => Cover t k a c
  -> Sieve a b
generatedSieve c = Sieve \g _ -> P.any (\(SomeLeg l) -> let f = legArrow l in factorsThrough g f \\ f \\ g) (legs c)

-- | Whether a sieve is the maximal one -- every arrow of the category is in it.
isMaximal :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> P.Bool
isMaximal s = P.and (sieveTable s)

-- | Whether every point of the second sieve is a point of the first.
contains :: forall {j} {k} (a :: k) (b :: j). (FiniteCat j, FiniteCat k) => Sieve a b -> Sieve a b -> P.Bool
contains s = \s' -> P.and (P.zipWith (\x y -> P.not y P.|| x) ts (sieveTable s'))
  where
    -- tabulated before the second sieve arrives, so a partial application tabulates @s@ once
    ts = sieveTable s

-- | Whether a sieve is covering: either it is the maximal sieve, or it contains the sieve that some
-- cover of its object generates.
--
-- That is the coverage taken at face value. It agrees with the Grothendieck topology the coverage
-- generates only when the covers are stable and compose. When they do not, 'closure' stops being
-- idempotent, and 'Proarrow.Testing.Laws.testLawvereTierney' is where that shows up.
isCovering
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> P.Bool
isCovering s@Sieve{} = isMaximal s P.|| P.any (\(SomeCover c) -> inS (generatedSieve @t @a @b c)) (covers @t @k @a)
  where
    -- applied to @s@ once, so it is not tabulated again for every cover
    inS = contains s

-- | The Lawvere–Tierney closure of a sieve: the pairs @(g, h)@ along which it pulls back to a
-- covering one. A sieve is covering exactly when its closure is the maximal sieve.
--
-- Note /both/ components -- @'dimap' g h@, not just @'lmap' g@. A coverage constrains only the
-- contravariant side, but a sieve over @j '+->' k@ has two, which is why @Props.Sheaf@ checks this
-- function's naturality at a non-trivial @j@.
closure
  :: forall t {j} {k} (a :: k) (b :: j)
   . (HasFiniteCovers t k, FiniteCat j, FiniteCat k)
  => Sieve a b
  -> Sieve a b
closure s@Sieve{} = Sieve \g h -> isCovering @t (dimap g h s) \\ g \\ h

-- | The coverage as a Lawvere–Tierney topology on the topos of finitary profunctors: 'closure', as
-- an arrow on the subobject classifier.
lawvereTierney
  :: forall t j k. (HasFiniteCovers t k, FiniteCat j, FiniteCat k) => (Omega :: PROD (FINITARY j k)) ~> Omega
lawvereTierney = Prod (Sub (Prof \s@Sieve{} -> closure @t s))

-- | Whether a finitary profunctor is a sheaf for the coverage: at every pair of objects and every
-- cover, restriction is a bijection from the elements at the covered object to the matching
-- families on the sieve the cover generates.
isSheaf
  :: forall t {j} {k} (p :: j +-> k)
   . (HasFiniteCovers t k, Finitary p, FiniteCat j, FiniteCat k)
  => P.Bool
isSheaf =
  P.and
    ( foreachOb @k \ @a ->
        let cs = covers @t @k @a -- does not depend on @b@, so bound outside the inner walk
        in foreachOb @j \ @b -> [sheafAt @t @p @a @b c | SomeCover c <- cs]
    )

-- | The sheaf condition at one cover: the restrictions of the elements at the covered object are
-- exactly the matching families, as multisets. A matching family /is/ a natural transformation out
-- of the generated sieve, so both sides come from the sieve viewed as a subobject of the
-- representable.
--
-- The 'P.error' branch is unreachable for any coverage, lawful or not: the membership test
-- 'generatedSieve' builds ignores its covariant argument and is closed under precomposition, so the
-- closure 'withSubobject' asks for holds by construction. Reaching it would take a 'Finitary'
-- instance on the hom-profunctor whose 'elements' omits an arrow, which
-- 'Proarrow.Testing.Laws.testFinitary' rules out.
sheafAt
  :: forall t {j} {k} (p :: j +-> k) (a :: k) (b :: j) c
   . (Site t k, Finitary p, FiniteCat j, FiniteCat k, Ob a, Ob b)
  => Cover t k a c
  -> P.Bool
sheafAt c = case generatedSieve @t @a @b c of
  Sieve s ->
    -- The sieve, reified as a subobject of the representable. 'withSubobject' checks the closure a
    -- sieve must have and hands back the inclusion, so the matching families are literally the
    -- natural transformations out of it -- no separate treatment of the points outside the sieve,
    -- and no argument needed about which naturality conditions may be dropped.
    withSubobject @(Yo a (OP b))
      (\(Yo g h) -> s g h)
      ( \ @q (Sub (Prof incl)) ->
          sort [natTable @q @p (\y -> case incl y of Yo g h -> dimap g h x) | x <- elements @p @a @b]
            P.== sort (natElements @q @p)
      )
      (P.error "sheafAt: the cover does not generate a sieve")
