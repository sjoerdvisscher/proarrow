{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Profunctors whose hom-sets are finite and numbered: @p a b@ is in bijection with an initial
-- segment of the naturals. This makes limits and colimits computable: an element is an index, so a
-- subset or quotient of a hom-set is a table of indices, which can be reified into a fresh object.
--
-- The numbering is a /value/, as in "Proarrow.Category.Instance.FinHask". A type-level size could
-- only be a formula in the sizes it is built from, which rules out constructions whose count
-- depends on how arrows compose, such as the exponential and the subobject classifier.
--
-- A 'Proarrow.Category.Enriched.Thin.DecidableProfunctor' is the special case where every size is
-- zero or one; 'decidableSize' and 'decidableFromIndex' build that instance.
--
-- This module is only the vocabulary. The category @'Proarrow.Category.Enriched.Finitary.Topos.FINITARY' j k@
-- and everything computed in it live in "Proarrow.Category.Enriched.Finitary.Topos". The class
-- and 'Elt' are needed by 'Proarrow.Limit.Power.Powered', "Proarrow.Category.Enriched" and
-- others that the topos half itself depends on.
module Proarrow.Category.Enriched.Finitary where

import Data.Kind (Constraint)
import Data.List (elemIndex, find, genericIndex, genericTake)
import Data.Maybe (isJust)
import Data.Type.Nat (snat)
import Data.Type.Nat qualified as N
import Data.Universe.Class qualified as U
import Data.Universe.Helpers qualified as U
import Numeric.Natural (Natural)
import Prelude (Maybe (..), compare, show, (+), (-), (<), (==))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin
  ( DecidableProfunctor (..)
  , Decision (..)
  , Enumerable (..)
  , Finite (..)
  , Indexed (..)
  , IndexedList (..)
  )
import Proarrow.Category.Instance.Bool (Booleans)
import Proarrow.Category.Instance.Opposite (OPPOSITE (..), Op (..))
import Proarrow.Category.Instance.Ordinal (LTE)
import Proarrow.Category.Instance.Product ((:**:) (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core (CategoryOf (..), Hom, Profunctor (..), Promonad (..), type (+->))
import Proarrow.Profunctor.Instance.Coproduct ((:+:) (..))
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Instance.Product ((:*:) (..))
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))

-- | A profunctor with finite, numbered hom-sets. 'toIndex' and 'fromIndex' are inverse for indices
-- below 'size'; @fromIndex@ of anything else is an error, as is 'toIndex' of an element that is not
-- one the instance can produce (which only an unlawfully built value can be).
--
-- An instance whose elements are found by searching should define 'elements' and read 'size' off
-- it, rather than let the default call 'fromIndex' once per element and repeat the search each time.
type Finitary :: forall {j} {k}. j +-> k -> Constraint
class (Profunctor p) => Finitary (p :: j +-> k) where
  -- | How many elements the hom-set has.
  size :: (Ob (a :: k), Ob (b :: j)) => Natural

  -- | Where an element sits in 'elements'. Takes its objects like the others do, so that an
  -- instance that has to search can bind the search outside the argument lambda and a caller can
  -- share it with @let toIndexP = 'toIndex' \@p \@a \@b@.
  toIndex :: (Ob (a :: k), Ob (b :: j)) => p a b -> Natural

  -- | The element at a position.
  fromIndex :: (Ob (a :: k), Ob (b :: j)) => Natural -> p a b

  -- | All elements of a hom-set, in index order.
  elements :: (Ob (a :: k), Ob (b :: j)) => [p a b]
  elements @a @b = P.map (fromIndex @p) (indices (size @p @a @b))

-- | @[0 .. n-1]@, which @n@ being a 'Natural' rules out writing directly.
indices :: Natural -> [Natural]
indices n = genericTake n [0 ..]

-- | A finitary profunctor's hom-set sizes, one per pair of objects, the outer index running over
-- @k@ and the inner over @j@. Cheap enough to display an object by: a presheaf on the graph
-- schema, say, shows as @[2,4,2,4]@.
sizes :: forall {j} {k} (p :: j +-> k). (Finitary p, Enumerable j, Enumerable k) => [Natural]
sizes = foreachOb @k \ @a -> foreachOb @j \ @b -> [size @p @a @b]

-- | The position of an object in its kind's object list.
objIndex :: forall {k} (a :: k). (Enumerable k, Ob a) => Natural
objIndex = withIndex @k @a (N.snatToNatural (snat @(Index a)))

-- | Everything an enumeration of a kind's objects can do at each of them, concatenated.
foreachOb :: forall k r. (Enumerable k) => (forall (a :: k). (Ob a) => [r]) -> [r]
foreachOb f = go (finite @k)
  where
    go :: forall (as :: [k]). IndexedList as -> [r]
    go FNil = []
    go (FCons @a as) = withOb @k @a (f @a) P.++ go as

-- * Thin profunctors

-- | A decidable profunctor has one element where it holds and none where it does not. These cannot
-- be @default@ method bodies: 'size' and 'fromIndex' do not mention their objects except in a
-- constraint, so GHC cannot tie a default body's objects to the instance's.
decidableSize :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (DecidableProfunctor p, Ob a, Ob b) => Natural
decidableSize = case decide @p @a @b of
  Yes _ -> 1
  No -> 0

decidableFromIndex
  :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (DecidableProfunctor p, Ob a, Ob b) => Natural -> p a b
decidableFromIndex _ = case decide @p @a @b of
  Yes x -> x
  No -> P.error "fromIndex: the profunctor does not hold here"

-- * Hom-sets as finite sets

-- | An element of a hom-set of @p@, viewed as an element of a /finite set/: every instance the
-- @universe@ package asks for is supplied by the numbering, with 'toIndex' standing in for equality
-- and ordering. So a finitary profunctor is a profunctor enriched in
-- 'Proarrow.Category.Instance.FinHask.FINHASK'.
newtype Elt (p :: j +-> k) (a :: k) (b :: j) = Elt {unElt :: p a b}

instance (Finitary p, Ob a, Ob b) => U.Universe (Elt (p :: j +-> k) a b) where
  universe = P.map Elt (elements @p)

instance (Finitary p, Ob a, Ob b) => U.Finite (Elt (p :: j +-> k) a b) where
  cardinality = U.Tagged (size @p @a @b)

instance (Finitary p) => P.Eq (Elt (p :: j +-> k) a b) where
  Elt x == Elt y = (toIndex x == toIndex y) \\ x

instance (Finitary p) => P.Ord (Elt (p :: j +-> k) a b) where
  compare (Elt x) (Elt y) = P.compare (toIndex x) (toIndex y) \\ x

instance (Finitary p) => P.Show (Elt (p :: j +-> k) a b) where
  show (Elt x) = P.show (toIndex x) \\ x

-- | A category whose hom-sets are finite: the 'Finitary' counterpart of
-- 'Proarrow.Category.Enriched.Thin.Decidable', and one half of 'FiniteCat'.
class (CategoryOf k, Finitary (Hom k)) => LocallyFinite k

instance (CategoryOf k, Finitary (Hom k)) => LocallyFinite k

-- | How an arrow factors through another into the same object: @'factorThrough' g f@ is an @h@
-- with @g = f '.' h@, if there is one. Only the hom-set @x '~>' y@ is searched, so only the
-- hom-sets need to be finite. An element is in the image of @f@ iff it factors through @f@.
factorThrough
  :: forall {k} (x :: k) y a. (LocallyFinite k, Ob x, Ob y, Ob a) => x ~> a -> y ~> a -> Maybe (x ~> y)
factorThrough g f = find (\h -> toIndex @(Hom k) @x @a (f . h) == gi) (elements @(Hom k) @x @y)
  where
    -- hoisted out of the lambda, as 'toIndex' asks: an instance that searches only searches once
    gi = toIndex g

-- | Whether an arrow factors through another, which is 'factorThrough' with the witness dropped.
-- 'Proarrow.Category.Enriched.Finitary.Sheaf.generatedSieve' is the caller: a cover's sieve is the
-- arrows that factor through one of its legs.
factorsThrough :: forall {k} (x :: k) y a. (LocallyFinite k, Ob x, Ob y, Ob a) => x ~> a -> y ~> a -> P.Bool
factorsThrough g f = isJust (factorThrough g f)

-- | A finite category: finitely many objects, and finitely many arrows between them. The first is
-- 'Enumerable', the second does not follow from it, and the enumeration below needs both.
class (Enumerable k, Finitary (Hom k)) => FiniteCat k

instance (Enumerable k, Finitary (Hom k)) => FiniteCat k

-- | A profunctor between categories with finite hom-sets is finitary iff it is enriched in finite
-- sets. These build a 'Finitary' instance from 'U.Finite' hom-sets, the counterparts of
-- 'decidableSize' and 'decidableFromIndex' one level up.
--
-- 'finiteToIndex' and 'finiteFromIndex' search 'U.universeF', which is fine for small hom-sets.
-- For large ones compute the index arithmetically, as
-- 'Proarrow.Category.Instance.FinHask.FinHask' does.
finiteSize :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (U.Finite (p a b)) => Natural
finiteSize = U.unTagged (U.cardinality @(p a b))

finiteToIndex :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (U.Finite (p a b), P.Eq (p a b)) => p a b -> Natural
finiteToIndex x = case elemIndex x U.universeF of
  Just i -> P.fromIntegral i
  Nothing -> P.error "toIndex: not in the universe of the hom-set"

finiteFromIndex :: forall {j} {k} (p :: j +-> k) (a :: k) (b :: j). (U.Finite (p a b)) => Natural -> p a b
finiteFromIndex i = genericIndex (U.universeF @(p a b)) i

-- | The one-object category has one arrow.
instance Finitary Unit where
  size = 1
  toIndex Unit = 0
  fromIndex _ = Unit

-- | @'Proarrow.Category.Instance.Bool.BOOL'@ is thin, so each hom-set holds at most the one arrow.
instance Finitary Booleans where
  size @a @b = decidableSize @Booleans @a @b
  toIndex _ = 0
  fromIndex @a @b = decidableFromIndex @Booleans @a @b

-- | The ordinals are thin too, so the same three lines serve. So a chain can be used as a site: a
-- cover there can have a leg that is itself covered, which no coverage on a two-object category
-- can arrange.
instance Finitary LTE where
  size @a @b = decidableSize @LTE @a @b
  toIndex _ = 0
  fromIndex @a @b = decidableFromIndex @LTE @a @b

-- * Products and coproducts

-- | The terminal profunctor has one element everywhere.
instance (CategoryOf j, CategoryOf k) => Finitary (TerminalProfunctor :: j +-> k) where
  size = 1
  toIndex TerminalProfunctor = 0
  fromIndex _ = TerminalProfunctor

-- | A pair of indices as one index, row-major: the first factor varies slowest. Shared by the two
-- instances that number a pair of independent choices (the product profunctor and the Yoneda
-- embedding), because 'ExpWeight' nests one inside the other, so they have to agree.
pairIndex :: Natural -> Natural -> Natural -> Natural
pairIndex n i j = i P.* n + j

-- | The inverse, given the size of the second factor.
unpairIndex :: Natural -> Natural -> (Natural, Natural)
unpairIndex 0 _ = P.error "fromIndex: a factor of the pair has no elements"
unpairIndex n i = i `P.divMod` n

instance (Finitary p, Finitary q) => Finitary (p :*: q) where
  size @a @b = size @p @a @b P.* size @q @a @b
  toIndex @a @b (x :*: y) = pairIndex (size @q @a @b) (toIndex x) (toIndex y)
  fromIndex @a @b i = let (l, r) = unpairIndex (size @q @a @b) i in fromIndex l :*: fromIndex r

  -- Spelled out, not left to the default: that would ask @p@ for its size once per element, and
  -- when @p@ is itself an enumeration ('Sieve', or a nested internal hom) a size is a whole search.
  elements @a @b = [x :*: y | x <- elements @p @a @b, y <- elements @q @a @b]

-- | The product of two finitary profunctors on the product of their kinds, numbered as ':*:' is.
instance (Finitary p, Finitary q) => Finitary (p :**: q) where
  size @'(a1, a2) @'(b1, b2) = size @p @a1 @b1 P.* size @q @a2 @b2
  toIndex @'(_, a2) @'(_, b2) (x :**: y) = pairIndex (size @q @a2 @b2) (toIndex x) (toIndex y)
  fromIndex @'(_, a2) @'(_, b2) i = let (l, r) = unpairIndex (size @q @a2 @b2) i in fromIndex l :**: fromIndex r
  elements @'(a1, a2) @'(b1, b2) = [x :**: y | x <- elements @p @a1 @b1, y <- elements @q @a2 @b2]

-- | The opposite of a finitary profunctor is finitary, at the same sizes read the other way round.
-- Taking @p = 'Hom' k@ this makes @'OPPOSITE' k@ a 'FiniteCat' whenever @k@ is one, so everything
-- computed for a finite site is available on the opposite category too. (This instance lives here
-- rather than with 'Op' because "Proarrow.Category.Instance.Opposite" sits below this module in the
-- import graph.)
instance (Finitary p) => Finitary (Op p) where
  size @(OP a) @(OP b) = size @p @b @a
  toIndex @(OP a) @(OP b) (Op x) = toIndex @p @b @a x
  fromIndex @(OP a) @(OP b) i = Op (fromIndex @p @b @a i)
  elements @(OP a) @(OP b) = P.map Op (elements @p @b @a)

-- | The initial profunctor has no elements anywhere.
instance (CategoryOf j, CategoryOf k) => Finitary (InitialProfunctor :: j +-> k) where
  size = 0
  toIndex = \case {}
  fromIndex _ = P.error "fromIndex: the initial profunctor has no elements"

-- | The indices of @p@ first, then those of @q@.
instance (Finitary p, Finitary q) => Finitary (p :+: q) where
  size @a @b = size @p @a @b + size @q @a @b
  toIndex @a @b = \case
    InjL x -> toIndex x
    InjR y -> size @p @a @b + toIndex y
  fromIndex @a @b i = if i < size @p @a @b then InjL (fromIndex i) else InjR (fromIndex (i - size @p @a @b))
