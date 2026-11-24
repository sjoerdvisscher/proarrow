-- | The walking bimonoid, the PROP for monoids and comonoids satisfying the
-- bimonoid compatibility laws. Objects count wires and tensor adds their counts.
-- An arrow records the paths between its inputs and outputs, in copy order at
-- each input and merge order at each output.
module Proarrow.Category.Instance.Bimonoid
  ( BIPATHS (..)
  , Bimonoid
  , Wire
  , fromOrderedPaths
  , orderedPaths
  ) where

import Control.Monad (guard)
import Data.Bifunctor (first)
import Data.Fin (Fin, weakenLeft, weakenRight)
import Data.List (sort)
import Data.Map.Strict qualified as M
import Data.Proxy (Proxy (..))
import Data.Type.Nat (Nat0, Nat1, Plus, snat, snatToNat)
import Data.Typeable (eqT)
import Data.Vec.Lazy qualified as V
import Prelude hiding (id, (**), (.))
import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.Simplex (IsNat, Nat)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (swap), associatorDefault)
import Proarrow.Category.Monoidal.Hypergraph (Sized (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Profunctor (..), Promonad (..), UN, WrappedOb, dimapDefault)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid qualified as Mon
import Proarrow.Optic.Iso (DecidableIso (..), isoFromEquality)

type data BIPATHS = BP Nat

type Wire :: BIPATHS
type Wire = BP Nat1

type Bimonoid :: CAT BIPATHS
data Bimonoid a b where
  Bimonoid :: (IsNat a, IsNat b) => V.Vec b [(Fin a, Int)] -> Bimonoid (BP a) (BP b)

deriving instance Eq (Bimonoid a b)
deriving instance Show (Bimonoid a b)

-- | Build an arrow from one list per output, in merge order. Each pair gives
-- the source input and its zero-based copy position. For each input the copy
-- positions must be consecutive starting at zero, with no repetitions.
--
-- >>> import Data.Fin (fin0)
-- >>> let crossed = [(fin0 :: Fin Nat1, 1), (fin0, 0)] V.::: V.VNil
-- >>> fmap orderedPaths (fromOrderedPaths crossed) == Just crossed
-- True
fromOrderedPaths :: (IsNat a, IsNat b) => V.Vec b [(Fin a, Int)] -> Maybe (Bimonoid (BP a) (BP b))
fromOrderedPaths paths = do
  let positions = M.fromListWith (++) [(input, [position]) | (input, position) <- concat paths]
  guard (all (\ps -> sort ps == [0 .. length ps - 1]) positions)
  pure (Bimonoid paths)

-- | The paths arriving at each output, in merge order.
orderedPaths :: Bimonoid (BP a) (BP b) -> V.Vec b [(Fin a, Int)]
orderedPaths (Bimonoid paths) = paths

permutationArrow :: (IsNat a, IsNat b) => V.Vec b (Fin a) -> Bimonoid (BP a) (BP b)
permutationArrow = Bimonoid P.. fmap (\i -> [(i, 0)])

instance CategoryOf BIPATHS where
  type (~>) = Bimonoid
  type Ob a = WrappedOb BP a

instance Profunctor Bimonoid where
  dimap = dimapDefault
  r \\ Bimonoid{} = r

instance Promonad Bimonoid where
  id = permutationArrow V.universe
  Bimonoid g . Bimonoid f =
    Bimonoid (rankPaths (fmap (concatMap (\(j, q) -> [(i, p, q) | (i, p) <- f V.! j])) g))

-- Copy order is lexicographic in the upstream and downstream copy positions.
rankPaths :: (Ord i) => V.Vec n [(i, Int, Int)] -> V.Vec n [(i, Int)]
rankPaths expanded = fmap (map (\key@(i, _, _) -> (i, positions M.! key))) expanded
  where
    byInput = M.fromListWith (++) [(i, [(p, q)]) | (i, p, q) <- concat expanded]
    positions =
      M.fromList
        [ ((i, p, q), pos)
        | (i, copies) <- M.toList byInput
        , (pos, (p, q)) <- zip [0 ..] (sort copies)
        ]

instance MonoidalProfunctor Bimonoid where
  one = Bimonoid V.VNil
  Bimonoid @a @b left ** Bimonoid @c @d right =
    withOb2 @Nat @a @c (withOb2 @Nat @b @d (Bimonoid (left' V.++ right')))
    where
      left' = fmap (map (first (weakenLeft (Proxy @c)))) left
      right' = fmap (map (first (weakenRight (Proxy @a)))) right

instance Monoidal BIPATHS where
  type Unit = BP Nat0
  type a ** b = BP (Plus (UN BP a) (UN BP b))
  withOb2 @(BP a) @(BP b) result = withOb2 @Nat @a @b result
  associator @a @b @c = associatorDefault @a @b @c
  associatorInv @a @b @c = associatorDefault @a @b @c

instance SymMonoidal BIPATHS where
  swap @(BP a) @(BP b) =
    withOb2 @Nat @a @b (withOb2 @Nat @b @a (permutationArrow (right V.++ left)))
    where
      right = fmap (weakenRight (Proxy @a)) (V.universe @b)
      left = fmap (weakenLeft (Proxy @b)) (V.universe @a)

instance DaggerProfunctor Bimonoid where
  dagger (Bimonoid @_ @b fibres) = Bimonoid (V.tabulate (\i -> map snd (sort (M.findWithDefault [] i byInput))))
    where
      byInput =
        M.fromListWith
          (++)
          [ (i, [(copyPosition, (j, mergePosition))])
          | (j, fibre) <- zip (V.toList (V.universe @b)) (V.toList fibres)
          , (mergePosition, (i, copyPosition)) <- zip [0 ..] fibre
          ]

instance HasInitialObject BIPATHS where
  type InitialObject = BP Nat0
  initiate = Bimonoid (V.repeat [])

instance HasTerminalObject BIPATHS where
  type TerminalObject = BP Nat0
  terminate = Bimonoid V.VNil

-- Tensor powers carry the componentwise multiplication of the generating wire.
instance (Ob (a :: BIPATHS)) => Mon.Monoid a where
  mempty = initiate
  mappend = withOb2 @Nat @(UN BP a) @(UN BP a) (Bimonoid (fmap pair V.universe))
    where
      n = Proxy @(UN BP a)
      pair :: Fin (UN BP a) -> [(Fin (Plus (UN BP a) (UN BP a)), Int)]
      pair i = [(weakenLeft n i, 0), (weakenRight n i, 0)]

instance (Ob (a :: BIPATHS)) => Mon.Comonoid a where
  counit = terminate
  comult = dagger Mon.mappend

instance DecidableIso BIPATHS where
  isoOf @_ @a @b = isoFromEquality (eqT @a @b)

instance Sized BIPATHS where
  sizeOf @(BP n) = fromIntegral (snatToNat (snat @n))
