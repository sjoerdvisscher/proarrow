{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | __Tensor networks__ as a hypergraph category: the same arrows as the matrices of
-- "Proarrow.Category.Instance.Mat", kept as a network instead of as one matrix. An object is a list
-- of dimensions, one for each wire. An arrow has nodes, each with a dimension, a node for each of its
-- input and output wires, and dense factors: flat vectors, each with a node for each of its axes. Its
-- entry at given indices of the wires is the sum, over the indices of the nodes that agree with
-- those of the wires, of the products of the entries of the factors.
--
-- So the structure of a hypergraph category costs nothing: identities, swaps, copying, merging,
-- discarding, cups and caps are wirings without factors, and the tensor puts factors side by side
-- without multiplying them. Composition glues the wirings and sums out the nodes that are no longer
-- on a wire, multiplying only the factors that a summed node joins. With "Proarrow.Tools.Einsum" a
-- network of tensors is contracted in the order its read-back chooses.
--
-- With the package's @blas@ flag, a contraction of two factors that is a matrix product is handed
-- to the system's BLAS (Accelerate on macOS, OpenBLAS elsewhere) at entries of type 'P.Double',
-- 'P.Float' and @'Complex' 'P.Double'@.
--
-- The biproducts are direct sums, a single wire whose dimension is the sum of the sizes of the two
-- objects. Their injections, projections and pairings are dense matrices, and so are the
-- distributors.
module Proarrow.Category.Instance.TensorNetwork
  ( TNET (..)
  , TensorNetwork
  , Scalar
  , dimsOf
  , Size
  , fromVector
  , toVector
  , fromEntries
  , entries
  ) where

import Data.Complex (Complex, conjugate)
import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Constraint, Type)
import Data.List qualified as List
import Data.Ord (comparing)
import Data.Proxy (Proxy (..))
import Data.Set qualified as Set
import Data.Type.Equality ((:~:) (..))
import Data.Vector.Storable qualified as SV
import Data.Vector.Storable.Mutable qualified as MSV
import Data.Vector.Unboxed qualified as UV
import Foreign.Storable (Storable)
import GHC.TypeNats (KnownNat, Nat, SNat, natVal, sameNat, withKnownNat, withSomeSNat, type (*), type (+))
import Unsafe.Coerce (unsafeCoerce)
import Prelude (Int, ($), (*), (+), (-), (==))
import Prelude qualified as P

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (..))
import Proarrow.Category.Instance.FinHask (unionFind)
import Proarrow.Category.Instance.TensorNetwork.Blas (Gemm, gemmComplexDouble, gemmDouble, gemmFloat)
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Action (MonoidalAction)
import Proarrow.Category.Monoidal.Closed (Closed (..))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosed (..), coactCC)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Dialogue (Dialogue (..))
import Proarrow.Category.Monoidal.Distributive (Distributive (..))
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, Hypergraph, Sized (..), cap, cup)
import Proarrow.Category.Monoidal.IsoMix (IsoMix (..))
import Proarrow.Category.Monoidal.StarAutonomous (ExpSA, StarAutonomous (..), applySA, currySA, expSA)
import Proarrow.Category.Monoidal.Strength (Costrong (..))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..), HasBiproducts)
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Is, Profunctor (..), Promonad (..), UN, dimapDefault, type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..))
import Proarrow.Object (KnownListOf (..), appendListOf, eqListOf, mapListOf, withKnownListOf, type (++))
import Proarrow.Optic.Iso (DecidableIso (..), isoFromEquality)

-- | The entries of the factors: numbers that can be stored unboxed. An instance needs no methods:
-- the loop that contracts factors is then compiled for its type.
type Scalar :: Type -> Constraint
class (P.Num e, Storable e) => Scalar e where
  -- | The entries of a contraction of two factors: given the dimension of each axis of the result
  -- and how far a step along it moves in the entries of each factor, the offset into each factor
  -- of each summed index, and the entries of the two factors, each entry is a sum of products.
  kernel :: [(Dim, Int, Int)] -> UV.Vector Index -> UV.Vector Index -> SV.Vector e -> SV.Vector e -> SV.Vector e
  -- inlined into each instance, so that the loop is specialised to its type
  kernel = contractLoop
  {-# INLINE kernel #-}

  -- | The conjugate of an entry, which the dagger takes: the identity on real numbers.
  conj :: e -> e
  conj = P.id

  -- | A fast matrix product, which a contraction of two factors that is one is handed to.
  gemm :: P.Maybe (Gemm e)
  gemm = P.Nothing

instance Scalar Int
instance Scalar P.Double where
  gemm = gemmDouble
instance Scalar P.Float where
  gemm = gemmFloat
instance Scalar (Complex P.Double) where
  conj = conjugate
  gemm = gemmComplexDouble

-- | The loop that 'kernel' runs, written once for every type: a loop over each axis of the result,
-- the last one innermost, reading the entries of both factors with their steps, and for each
-- entry a loop over the summed indices.
{-# INLINEABLE contractLoop #-}
contractLoop
  :: (P.Num e, Storable e)
  => [(Dim, Int, Int)] -> UV.Vector Index -> UV.Vector Index -> SV.Vector e -> SV.Vector e -> SV.Vector e
contractLoop steps !so !to !v !w = SV.create do
  out <- MSV.unsafeNew (P.product [d | (d, _, _) <- steps])
  let go [] !a !b !dst = MSV.unsafeWrite out dst (entry a b)
      go [(!d, !s, !t)] !a !b !dst
        | n == 1 = products 0 (a + so `UV.unsafeIndex` 0) (b + to `UV.unsafeIndex` 0)
        | P.otherwise = sums 0 a b
        where
          -- with nothing summed, each entry is one product
          products !i !x !y
            | i == d = P.pure ()
            | P.otherwise =
                MSV.unsafeWrite out (dst + i) (v `SV.unsafeIndex` x * w `SV.unsafeIndex` y) P.>> products (i + 1) (x + s) (y + t)
          sums !i !x !y
            | i == d = P.pure ()
            | P.otherwise = MSV.unsafeWrite out (dst + i) (entry x y) P.>> sums (i + 1) (x + s) (y + t)
      go ((!d, !s, !t) : rest) !a !b !dst = outer 0 a b
        where
          size' = P.product [e | (e, _, _) <- rest]
          outer !i !x !y
            | i == d = P.pure ()
            | P.otherwise = go rest x y (dst + i * size') P.>> outer (i + 1) (x + s) (y + t)
  go steps 0 0 0
  P.pure out
  where
    n = UV.length so
    -- the sum of the products at a place in each factor; its arguments are strict, so that the loop
    -- does not look them up again for every index
    entry !a !b = sumFrom 0 0
      where
        sumFrom !i !acc =
          if i == n
            then acc
            else
              sumFrom (i + 1) (acc + v `SV.unsafeIndex` (a + so `UV.unsafeIndex` i) * w `SV.unsafeIndex` (b + to `UV.unsafeIndex` i))

-- | A node of a network, numbered from 0.
type Node = Int

-- | The dimension of a wire or a node.
type Dim = Int

-- | An index along a wire or an axis, or a position in a factor's entries.
type Index = Int

-- | Objects are lists of dimensions, one for each wire.
type data TNET (e :: Type) = TN [Nat]

-- | The dimensions of a list, as numbers.
dimsOf :: forall ns. (KnownListOf KnownNat ns) => [Dim]
dimsOf = mapListOf @KnownNat (\ @n -> P.fromIntegral (natVal (Proxy @n))) (listOf @KnownNat @ns)

-- | A dense factor: its entries, row by row over its axes, and the node of each axis.
data Factor e = Factor {axes :: [Node], values :: SV.Vector e}

-- | The nodes, numbered from 0 with their dimensions, the node of each input and output wire, and
-- the factors. Kept so that every node is on a wire and no factor has an axis twice.
data Net e = Net {nodeDims :: [Dim], ins :: [Node], outs :: [Node], factors :: [Factor e]}

-- | An arrow between two lists of dimensions.
type TensorNetwork :: CAT (TNET e)
data TensorNetwork a b where
  TensorNetwork
    :: forall {e} as bs. (KnownListOf KnownNat as, KnownListOf KnownNat bs) => Net e -> TensorNetwork (TN as :: TNET e) (TN bs)

-- | A wiring without factors: nodes of the given dimensions, and the node of each input and output
-- wire.
wiring
  :: forall {e} as bs
   . (KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => [Dim] -> [Node] -> [Node] -> TensorNetwork (TN as :: TNET e) (TN bs)
wiring dims is os = TensorNetwork (Net dims is os [])

-- | The wires going straight through, between two lists of the same dimensions.
straight
  :: forall {e} as bs. (KnownListOf KnownNat as, KnownListOf KnownNat bs) => TensorNetwork (TN as :: TNET e) (TN bs)
straight = wiring (dimsOf @as) (wires @as) (wires @as)

-- | The arrow with the given entries, laid out as 'toVector' gives them. The length of the vector
-- must be the product of all the dimensions.
fromVector
  :: forall {e} as bs
   . (Scalar e, KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => SV.Vector e -> TensorNetwork (TN as :: TNET e) (TN bs)
fromVector vs
  | SV.length vs P./= P.product dims = P.error "fromVector: the length is not the product of the dimensions"
  | P.otherwise = TensorNetwork (Net dims is os [Factor (os P.++ is) vs])
  where
    dims = dimsOf @as P.++ dimsOf @bs
    is = wires @as
    os = [P.length is .. P.length dims - 1]

-- | The entries, row by row: a row for each index of the output wires and a column for each index
-- of the input wires, both with the last wire varying fastest. This relies on every node of the
-- network being on a wire, which composition keeps so.
toVector :: forall {e} a b. (Scalar e) => TensorNetwork (a :: TNET e) b -> SV.Vector e
toVector (TensorNetwork (Net dims is os fs))
  | distinct ws = values (product ws)
  | P.otherwise = SV.create do
      out <- MSV.replicate (extent dims ws) 0
      let vs = values (product order)
          go [] !src !dst = MSV.unsafeWrite out dst (vs `SV.unsafeIndex` src) P.>> P.pure (src + 1)
          go ((d, w) : rest) !src !dst = loop 0 src
            where
              loop !i !from
                | i == d = P.pure from
                | P.otherwise = go rest from (dst + i * w) P.>>= loop (i + 1)
      _ <- go [(dims P.!! n, P.sum [st | (x, st) <- P.zip ws wireStrides, x == n]) | n <- order] 0 0
      P.pure out
  where
    ws = os P.++ is
    -- the product of the factors, kept over the given nodes
    product keep = contract1 dims (case fs of [] -> unit; f : rest -> P.foldl times f rest) keep []
    times g h = contract dims g h (nubOrd (axes g P.++ axes h)) []
    -- with a node on several wires, each entry of the product over the nodes goes to the place
    -- that its wires give it, and the others are 0
    order = nubOrd ws
    wireStrides = P.drop 1 (P.scanr (*) 1 (P.fmap (dims P.!!) ws))

-- | The arrow with the given rows of entries, laid out as 'entries' gives them.
fromEntries
  :: forall {e} as bs
   . (Scalar e, KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => [[e]] -> TensorNetwork (TN as :: TNET e) (TN bs)
fromEntries rows = fromVector (SV.fromList (P.concat rows))

-- | The entries as rows, as 'toVector' lays them out.
entries :: forall {e} a b. (Scalar e) => TensorNetwork (a :: TNET e) b -> [[e]]
entries f@(TensorNetwork @as @bs _) = [SV.toList (SV.slice (r * ni) ni v) | r <- [0 .. size @bs - 1]]
  where
    v = toVector f
    ni = size @as

-- | The matrix of a function from the indices of the inputs to those of the outputs: each column
-- has a 1 in the row the function gives it.
reindex
  :: forall {e} as bs
   . (Scalar e, KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => (Index -> Index) -> TensorNetwork (TN as :: TNET e) (TN bs)
reindex f = fromVector (SV.generate (size @bs * ni) \k -> let (r, c) = k `P.quotRem` ni in if r == f c then 1 else 0)
  where
    ni = size @as

-- | The arrow with no entries, into or out of a wire of dimension 0.
zero
  :: forall {e} as bs
   . (Scalar e, KnownListOf KnownNat as, KnownListOf KnownNat bs)
  => TensorNetwork (TN as :: TNET e) (TN bs)
zero = fromVector SV.empty

-- | The size of a list of dimensions: their product.
type Size :: [Nat] -> Nat
type family Size ns where
  Size '[] = 1
  Size (n ': ns) = n * Size ns

-- | The size of a list of dimensions, as a number.
size :: forall ns. (KnownListOf KnownNat ns) => Int
size = P.product (dimsOf @ns)

-- | The dimension of the direct sum of two lists of dimensions.
withSum
  :: forall as bs r. (KnownListOf KnownNat as, KnownListOf KnownNat bs) => ((KnownNat (Size as + Size bs)) => r) -> r
withSum = withKnownNat n
  where
    n :: SNat (Size as + Size bs)
    n = withSomeSNat (P.fromIntegral (size @as + size @bs)) unsafeCoerce

-- | The product of two factors, with the given nodes kept, in that order, and the others summed.
contract :: forall e. (Scalar e) => [Dim] -> Factor e -> Factor e -> [Node] -> [Node] -> Factor e
contract dims f g keep summed
  | P.Just mm <- gemm, P.Just r <- viaGemm mm dims f g keep summed = r
  | P.otherwise =
      Factor
        keep
        ( kernel
            [(dims P.!! x, stride dims f x, stride dims g x) | x <- keep]
            (offsets f summed)
            (offsets g summed)
            (values f)
            (values g)
        )
  where
    -- the offset into a factor's entries of each index of the given nodes
    offsets h = P.foldl (\acc x -> step acc (dims P.!! x) (stride dims h x)) (UV.singleton 0)
    step acc d s = UV.generate (UV.length acc * d) \j -> let (q, r) = j `P.quotRem` d in acc `UV.unsafeIndex` q + r * s

-- | One factor with the given nodes kept, in that order, and the others summed: its product with the
-- unit. A factor with an axis twice gives its diagonal, and the entries are the same along a kept
-- node that it does not have.
contract1 :: (Scalar e) => [Dim] -> Factor e -> [Node] -> [Node] -> Factor e
contract1 dims f keep summed
  | P.null summed P.&& axes f == keep = f
  | P.otherwise = contract dims f unit keep summed

-- | The factor without axes whose entry is 1.
unit :: (P.Num e, Storable e) => Factor e
unit = Factor [] (SV.singleton 1)

-- | A contraction of two factors as a matrix product, when it is one: something is summed, every
-- summed node is on both factors, and the kept nodes of the first come before those of the second,
-- or after them, as the transposed product. A factor whose axes are in neither the order of its
-- matrix nor that of its transpose is rearranged first.
viaGemm :: (Scalar e) => Gemm e -> [Dim] -> Factor e -> Factor e -> [Node] -> [Node] -> P.Maybe (Factor e)
viaGemm mm dims f g keep summed
  | P.not (matrixProduct f g summed) P.|| rows * cols * inner P.< gemmWork = P.Nothing
  | keep == ms P.++ ns = P.Just (Factor keep (mm ta tb rows cols inner va vb))
  | keep == ns P.++ ms = P.Just (Factor keep (mm (P.not tb) (P.not ta) cols rows inner vb va))
  | P.otherwise = P.Nothing
  where
    ms = [x | x <- axes f, P.not (onFactor x g)]
    ns = [x | x <- axes g, P.not (onFactor x f)]
    ss = P.filter (`P.elem` summed) (axes f)
    rows = extent dims ms
    cols = extent dims ns
    inner = extent dims ss
    (ta, va) = matrix f ms ss
    (tb, vb) = matrix g ss ns
    -- a factor as a matrix with the first nodes as rows: transposed, or rearranged when it is not
    -- already in that order
    matrix h rs cs
      | axes h == cs P.++ rs = (P.True, values h)
      | P.otherwise = (P.False, values (contract1 dims h (rs P.++ cs) []))

-- | How far a step along a node moves in a factor's entries: the strides of its axes on that node,
-- 0 when it has none.
stride :: [Dim] -> Factor e -> Node -> Int
stride dims f node = P.sum [s | (a, s) <- P.zip (axes f) (P.drop 1 (P.scanr (*) 1 (P.fmap (dims P.!!) (axes f)))), a == node]

-- | Whether no element of the list is there twice.
distinct :: [Node] -> P.Bool
distinct = go IS.empty
  where
    go _ [] = P.True
    go seen (x : xs) = P.not (x `IS.member` seen) P.&& go (IS.insert x seen) xs

-- | Whether the node is on one of the factor's axes.
onFactor :: Node -> Factor e -> P.Bool
onFactor x f = x `P.elem` axes f

-- | Whether a product of two factors that sums the given nodes is a matrix product: something is
-- summed, and the nodes on both factors are the summed ones.
matrixProduct :: Factor e -> Factor e -> [Node] -> P.Bool
matrixProduct f g summed = P.not (P.null summed) P.&& Set.fromList [x | x <- axes f, onFactor x g] == Set.fromList summed

-- | The number of indices of the given nodes together.
extent :: [Dim] -> [Node] -> Int
extent dims = P.product P.. P.fmap (dims P.!!)

-- | The number of multiplications from which a matrix product goes to 'gemm'.
gemmWork :: Int
gemmWork = 4096

-- | The network with every factor's axes distinct, every node that is on no wire summed out, and
-- the nodes renumbered.
normalize :: (Scalar e) => Net e -> Net e
normalize (Net dims is os fs) =
  Net
    (P.fmap (dims P.!!) kept)
    (P.fmap renumber is)
    (P.fmap renumber os)
    (P.fmap relabel (scalars (loops P.++ sumOut reduced shared)))
  where
    summed = [n | n <- [0 .. P.length dims - 1], n `Set.notMember` keptSet]
    -- the number of factors on each node
    factorsOn n = IM.findWithDefault 0 n counts
    distinctAxes = [(f, nubOrd (axes f)) | f <- fs]
    counts = IM.fromListWith (+) [(m, 1 :: Int) | (_, as) <- distinctAxes, m <- as]
    -- each factor with its axes distinct, and the summed nodes that no other factor has summed out
    reduced =
      [ let own = [m | m <- as, m `Set.notMember` keptSet, factorsOn m == 1] in contract1 dims f (as List.\\ own) own
      | (f, as) <- distinctAxes
      ]
    -- the summed nodes on no factor, as of closed loops: a scalar of their dimensions
    loops = case [n | n <- summed, factorsOn n == 0] of
      [] -> []
      ns -> [Factor [] (SV.singleton (P.fromIntegral (extent dims ns)))]
    shared = [n | n <- summed, factorsOn n P.> 1]
    -- the factors on a shared node multiplied two at a time, first the pair whose result grows least
    -- (its size less those of the two factors, as the read-back chooses), each node summed out by
    -- the product that brings together the last two factors on it
    sumOut gs [] = gs
    sumOut gs ns@(n : _) =
      let (touching, others) = List.partition (onFactor n) gs
          numbered = P.zip [0 :: Int ..] touching
          pairs = [(f, g, [h | (k, h) <- numbered, k P./= i, k P./= j] P.++ others) | (i, f) <- numbered, (j, g) <- numbered, i P.< j]
          product (f, g, outside) =
            let ds = [m | m <- ns, onFactor m f P.|| onFactor m g, P.not (P.any (onFactor m) outside)]
                left = nubOrd (axes f P.++ axes g) List.\\ ds
                -- a product that is not a matrix product puts the nodes that a later product sums
                -- last, where a matrix product wants them
                keep = if matrixProduct f g ds then left else let (later, now) = List.partition (`P.elem` ns) left in now P.++ later
            in (extent dims keep - extent dims (axes f) - extent dims (axes g), (contract dims f g keep ds, outside, ds))
          (_, (fg, rest, done)) = List.minimumBy (comparing P.fst) (P.fmap product pairs)
      in sumOut (fg : rest) (ns List.\\ done)
    -- the factors without axes multiplied into one
    scalars gs = case List.partition (P.null P.. axes) gs of
      (c : d : more, rest) -> Factor [] (SV.singleton (P.product [SV.head (values x) | x <- c : d : more])) : rest
      _ -> gs
    kept = nubOrd (is P.++ os)
    keptSet = Set.fromList kept
    renumber = renumbering kept
    relabel (Factor as vs) = Factor (P.fmap renumber as) vs

-- | The new number of each of the given nodes: its place in the list.
renumbering :: [Node] -> Node -> Node
renumbering ns = (IM.fromList (P.zip ns [0 ..]) IM.!)

-- | Two networks side by side.
besideNet :: Net e -> Net e -> Net e
besideNet (Net d1 i1 o1 f1) (Net d2 i2 o2 f2) =
  Net (d1 P.++ d2) (i1 P.++ P.fmap (+ k) i2) (o1 P.++ P.fmap (+ k) o2) (f1 P.++ P.fmap shift f2)
  where
    k = P.length d1
    shift (Factor as vs) = Factor (P.fmap (+ k) as) vs

-- | The second network after the first: their wirings glued along the wires in between, and the
-- nodes that are then on no wire summed out.
composeNet :: (Scalar e) => Net e -> Net e -> Net e
composeNet f g
  | P.Just through <- permutation g = f{outs = P.fmap (outs f P.!!) through}
  | P.Just through <- permutation (transposeNet f) = g{ins = P.fmap (ins g P.!!) through}
  | P.otherwise =
      normalize
        ( Net
            [nodeDims both P.!! r | r <- live]
            (P.fmap node (ins f))
            (P.fmap (node P.. (+ k)) (outs g))
            [Factor (P.fmap node as) vs | Factor as vs <- factors both]
        )
  where
    both = besideNet f g
    k = P.length (nodeDims f)
    find = unionFind (P.zip (outs f) (P.fmap (+ k) (ins g)))
    -- the nodes that are left after gluing, numbered from 0
    live = nubOrd [find n | n <- [0 .. P.length (nodeDims both) - 1]]
    node = renumbering live P.. find

-- | For a wiring without factors whose every node has one input wire and at least one output wire,
-- such as a permutation or copying: the input wire that each output wire continues.
permutation :: Net e -> P.Maybe [Int]
permutation (Net _ is os fs)
  | P.not (P.null fs) P.|| P.not (distinct is) = P.Nothing
  | is == os = P.Just [0 .. P.length is - 1]
  | Set.fromList is == Set.fromList os = P.Just (P.fmap (renumbering is) os)
  | P.otherwise = P.Nothing

-- | The network the other way round.
transposeNet :: Net e -> Net e
transposeNet (Net d i o fs) = Net d o i fs

withAppend
  :: forall as bs r. (KnownListOf KnownNat as, KnownListOf KnownNat bs) => ((KnownListOf KnownNat (as ++ bs)) => r) -> r
withAppend = withKnownListOf (appendListOf (listOf @KnownNat @as) (listOf @KnownNat @bs))

withAssoc
  :: forall as bs cs r
   . (KnownListOf KnownNat as, KnownListOf KnownNat bs, KnownListOf KnownNat cs)
  => ((KnownListOf KnownNat ((as ++ bs) ++ cs), KnownListOf KnownNat (as ++ (bs ++ cs))) => r) -> r
withAssoc r = withAppend @as @bs (withAppend @(as ++ bs) @cs (withAppend @bs @cs (withAppend @as @(bs ++ cs) r)))

-- | The arrow the other way round: its wiring with inputs and outputs swapped.
transpose :: TensorNetwork (a :: TNET e) b -> TensorNetwork b a
transpose (TensorNetwork n) = TensorNetwork (transposeNet n)

instance (Scalar e) => Profunctor (TensorNetwork :: CAT (TNET e)) where
  dimap = dimapDefault
  r \\ TensorNetwork{} = r

instance (Scalar e) => Promonad (TensorNetwork :: CAT (TNET e)) where
  id = straight
  TensorNetwork g . TensorNetwork f = TensorNetwork (composeNet f g)

-- | Tensor networks with entries @e@, between lists of dimensions.
instance (Scalar e) => CategoryOf (TNET e) where
  type (~>) = TensorNetwork
  type Ob a = (Is TN a, KnownListOf KnownNat (UN TN a))

-- | The conjugate transpose. 'dual' is the transpose without conjugating, since the compact-closed
-- structure is bilinear.
instance (Scalar e) => DaggerProfunctor (TensorNetwork :: CAT (TNET e)) where
  dagger (TensorNetwork n) = TensorNetwork (transposeNet n){factors = [Factor as (SV.map conj vs) | Factor as vs <- factors n]}

-- | A wire of dimension 0.
instance (Scalar e) => HasInitialObject (TNET e) where
  type InitialObject = TN '[0]
  initiate = zero

-- | A wire of dimension 0.
instance (Scalar e) => HasTerminalObject (TNET e) where
  type TerminalObject = TN '[0]
  terminate = zero

-- | The direct sum, as a single wire: the transpose of the product.
instance (Scalar e) => HasBinaryCoproducts (TNET e) where
  type a || b = TN '[Size (UN TN a) + Size (UN TN b)]
  withObCoprod @(TN as) @(TN bs) r = withSum @as @bs r
  lft @(TN as) @(TN bs) = withSum @as @bs (reindex P.id)
  rgt @(TN as) @(TN bs) = withSum @as @bs (reindex (size @as +))
  f ||| g = transpose (transpose f &&& transpose g)

-- | The direct sum, as a single wire: the entries of the first arrow above those of the second.
instance (Scalar e) => HasBinaryProducts (TNET e) where
  type a && b = TN '[Size (UN TN a) + Size (UN TN b)]
  withObProd @(TN as) @(TN bs) r = withSum @as @bs r
  fst @a @b = transpose (lft @_ @a @b)
  snd @a @b = transpose (rgt @_ @a @b)
  f@(TensorNetwork @_ @as _) &&& g@(TensorNetwork @_ @bs _) = withSum @as @bs (fromVector (toVector f SV.++ toVector g))

instance (Scalar e) => HasBiproducts (TNET e)

instance (Scalar e) => MonoidalProfunctor (TensorNetwork :: CAT (TNET e)) where
  one = id
  TensorNetwork @as @bs f ** TensorNetwork @cs @ds g = withAppend @as @cs (withAppend @bs @ds (TensorNetwork (besideNet f g)))

-- | The wires side by side as the tensor: on matrices, the Kronecker product.
instance (Scalar e) => Monoidal (TNET e) where
  type Unit = TN '[]
  type a ** b = TN (UN TN a ++ UN TN b)
  withOb2 @(TN as) @(TN bs) r = withAppend @as @bs r
  leftUnitor = id
  leftUnitorInv = id
  rightUnitor @(TN as) = withAppend @as @'[] straight
  rightUnitorInv @(TN as) = withAppend @as @'[] straight
  associator @(TN as) @(TN bs) @(TN cs) = withAssoc @as @bs @cs straight
  associatorInv @(TN as) @(TN bs) @(TN cs) = withAssoc @as @bs @cs straight

instance (Scalar e) => SymMonoidal (TNET e) where
  swap @(TN as) @(TN bs) =
    withAppend @as @bs $
      withAppend @bs @as $
        let na = P.length (dimsOf @as)
            nb = P.length (dimsOf @bs)
        in wiring (dimsOf @as P.++ dimsOf @bs) [0 .. na P.+ nb - 1] ([na .. na P.+ nb - 1] P.++ [0 .. na - 1])

-- | The distributors reorder the entries of the direct sums.
instance (Scalar e) => Distributive (TNET e) where
  distL @(TN as) @(TN bs) @(TN cs) =
    withSum @bs @cs $
      withAppend @as @'[Size bs + Size cs] $
        withAppend @as @bs $
          withAppend @as @cs $
            withSum @(as ++ bs) @(as ++ cs) $
              let (sa, sb, sc) = (size @as, size @bs, size @cs)
                  target c = let (i, k) = c `P.quotRem` (sb + sc) in if k P.< sb then i * sb + k else sa * sb + i * sc + k - sb
              in reindex target
  distR @(TN as) @(TN bs) @(TN cs) =
    withSum @as @bs $
      withAppend @as @cs $
        withAppend @bs @cs $
          withSum @(as ++ cs) @(bs ++ cs) $
            reindex P.id
  absorbL @(TN as) = withAppend @as @'[0] zero
  absorbR = zero

-- | Every object is self-dual, with the transpose as the dual of an arrow: its wiring the other way
-- round.
instance (Scalar e) => Dialogue (TNET e) where
  type Dual a = a
  withObDual r = r
  dual = transpose
  linDist @(TN as) @(TN bs) @(TN cs) (TensorNetwork (Net d i o f)) =
    withAppend @bs @cs $ let na = P.length (dimsOf @as) in TensorNetwork (Net d (P.take na i) (P.drop na i P.++ o) f)
  linDistInv @(TN as) @(TN bs) (TensorNetwork (Net d i o f)) =
    withAppend @as @bs $ let nb = P.length (dimsOf @bs) in TensorNetwork (Net d (i P.++ P.take nb o) (P.drop nb o) f)
  doubleNegInv = id

instance (Scalar e) => StarAutonomous (TNET e) where
  dualInv = transpose
  doubleNeg = id

instance (Scalar e) => Closed (TNET e) where
  type a ~~> b = ExpSA a b
  withObExp @(TN as) @(TN bs) r = withAppend @as @bs r
  curry @a @b = currySA @a @b
  apply @a @b = applySA @a @b
  (^^^) = expSA

instance (Scalar e) => IsoMix (TNET e) where
  dualUnit = id
  dualUnitInv = id
  dualityCounit @a = cap @a

instance (Scalar e) => CompactClosed (TNET e) where
  distribDual @(TN as) @(TN bs) = withAppend @as @bs id
  dualityUnit @a = cup @a

instance (Scalar e, MonoidalAction (t :: (TNET e, TNET e) +-> TNET e)) => Costrong t (TensorNetwork :: CAT (TNET e)) where
  coact @x = coactCC @t @x

-- | Merging each wire with its partner, and the unit.
instance (Scalar e, KnownListOf KnownNat ns) => Monoid (TN ns :: TNET e) where
  mempty = wiring (dimsOf @ns) [] (wires @ns)
  mappend = withAppend @ns @ns (wiring (dimsOf @ns) (wires @ns P.++ wires @ns) (wires @ns))

-- | Copying each wire, and discarding.
instance (Scalar e, KnownListOf KnownNat ns) => Comonoid (TN ns :: TNET e) where
  counit = wiring (dimsOf @ns) (wires @ns) []
  comult = withAppend @ns @ns (wiring (dimsOf @ns) (wires @ns) (wires @ns P.++ wires @ns))

-- | A node for each wire of a list.
wires :: forall ns. (KnownListOf KnownNat ns) => [Node]
wires = [0 .. P.length (dimsOf @ns) - 1]

instance (Scalar e, KnownListOf KnownNat ns) => CommutativeMonoid (TN ns :: TNET e)
instance (Scalar e, KnownListOf KnownNat ns) => CocommutativeComonoid (TN ns :: TNET e)
instance (Scalar e, KnownListOf KnownNat ns) => Frobenius (TN ns :: TNET e)
instance (Scalar e) => Hypergraph (TNET e)
instance (Scalar e) => CopyDiscard (TNET e)

-- | The size of an object is the product of its dimensions.
instance (Scalar e) => Sized (TNET e) where
  sizeOf @(TN ns) = size @ns

-- | Two objects are isomorphic when they have the same dimensions.
instance (Scalar e) => DecidableIso (TNET e) where
  isoOf @_ @(TN as) @(TN bs) =
    isoFromEquality
      ( P.fmap
          (\Refl -> Refl)
          (eqListOf @KnownNat (\ @x @y -> sameNat (Proxy @x) (Proxy @y)) (listOf @KnownNat @as) (listOf @KnownNat @bs))
      )
