-- | A monoid as a one-object category: the single object 'M', with the monoid's elements
-- @'Unit' ~> m@ as the morphisms. Every universal construction collapses onto @M@, so for a
-- commutative monoid it is cartesian (hence 'CopyDiscard'), cocartesian, closed and compact
-- closed all at once.
module Proarrow.Category.Instance.Monoid where

import Data.Type.Nat (Nat (..))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Enumerable (..), Finite (..), Indexed (..), IndexedList (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomous (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), dimapDefault)
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..), combine)

type data MONOID (m :: k) = M
data Mon a b where
  Mon :: Unit ~> m -> Mon (M :: MONOID m) M
instance (Monoid m) => Profunctor (Mon :: CAT (MONOID m)) where
  dimap = dimapDefault
  r \\ Mon{} = r
instance (Monoid m) => Promonad (Mon :: CAT (MONOID m)) where
  id = Mon mempty
  Mon f . Mon g = Mon (combine f g)

-- | A monoid as a one object category.
instance (Monoid m) => CategoryOf (MONOID m) where
  type (~>) = Mon
  type Ob a = a P.~ M

instance (Monoid m) => HasInitialObject (MONOID m) where
  type InitialObject = M
  initiate = Mon mempty
instance (Monoid m) => HasTerminalObject (MONOID m) where
  type TerminalObject = M
  terminate = Mon mempty
instance (Monoid m) => HasBinaryProducts (MONOID m) where
  type a && b = M
  withObProd @M @M r = r
  fst @M @M = Mon mempty
  snd @M @M = Mon mempty
  Mon f &&& Mon g = Mon (combine f g)
instance (Monoid m) => HasBinaryCoproducts (MONOID m) where
  type a || b = M
  withObCoprod @M @M r = r
  lft @M @M = Mon mempty
  rgt @M @M = Mon mempty
  Mon f ||| Mon g = Mon (combine f g)

instance (CommutativeMonoid m) => MonoidalProfunctor (Mon :: CAT (MONOID m)) where
  one = Mon mempty
  Mon f ** Mon g = Mon (combine f g)
instance (CommutativeMonoid m) => Monoidal (MONOID m) where
  type Unit = M
  type M ** M = M
  withOb2 r = r
  leftUnitor = Mon mempty
  leftUnitorInv = Mon mempty
  rightUnitor = Mon mempty
  rightUnitorInv = Mon mempty
  associator = Mon mempty
  associatorInv = Mon mempty
instance (CommutativeMonoid m) => SymMonoidal (MONOID m) where
  swap = Mon mempty

instance (CommutativeMonoid m) => StarAutonomous (MONOID m) where
  type Dual (M :: MONOID m) = M
  withObDual r = r
  dual f@Mon{} = f
  dualInv f = f
  linDist _ = id
  linDistInv _ = id
instance (CommutativeMonoid m) => CompactClosed (MONOID m) where
  distribDual = Mon mempty
  dualUnit = Mon mempty
instance (CommutativeMonoid m) => Closed (MONOID m) where
  type a ~~> b = M
  withObExp r = r
  curry (Mon m) = Mon m
  apply = Mon mempty

instance (CommutativeMonoid m) => Comonoid (M :: MONOID m) where
  counit = Mon mempty
  comult = Mon mempty
instance (CommutativeMonoid m) => CocommutativeComonoid (M :: MONOID m)
instance (CommutativeMonoid m) => CopyDiscard (MONOID m)

-- | A monoid is a one-object category, so its kind has one inhabitant, at index zero. Said directly
-- rather than left to the 'Objects' default, so that it reduces for a not-yet-known inhabitant --
-- which is how 'withOb' learns there is only @'M'@.
instance Indexed (MONOID m) where
  type Index (a :: MONOID m) = 'Z

instance Finite (MONOID m) where
  type Objects (MONOID m) = '[M]
  finite = FCons FNil

instance (Monoid m) => Enumerable (MONOID m) where
  withIndex r = r
  withOb r = r
