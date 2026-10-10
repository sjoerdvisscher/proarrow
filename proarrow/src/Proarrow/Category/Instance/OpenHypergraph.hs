{-# LANGUAGE AllowAmbiguousTypes #-}

-- | __Open hypergraphs__ with typed wires: decorated cospans ("Proarrow.Category.Instance.DecoratedCospan")
-- of finite sets whose elements have sorts, decorated with labelled boxes. A morphism has nodes, each
-- of some sort, boxes attached to them, and two boundaries of sorted ports. It is a morphism of the
-- free hypergraph category on its boxes, and two such morphisms are equal by the Frobenius laws
-- exactly when they are 'isomorphic'.
--
-- The sorts are objects of a category @s@, known at runtime, so that a computed apex knows the sorts
-- of its nodes. A list of sorts @xs@ gives the boundary @'Wires' xs@. Comparing two open hypergraphs,
-- or checking sorts given from outside, asks whether two sorts are isomorphic ('DecidableIso').
module Proarrow.Category.Instance.OpenHypergraph
  ( -- * Sorts
    SomeSort
  , SortOb
  , Sorted
  , PortSorts
  , sortOf
  , Sorts
  , SortList
  , sorts
  , sortList
  , Port (..)
  , SORTED
  , reifySorts

    -- * Open hypergraphs
  , OPENHG
  , Wires
  , Box (..)
  , Boxes (..)
  , WireSorts
  , box
  , openHypergraph
  , unsafeOpenHypergraph
  , isomorphic
  , sameSort

    -- * Read-back
  , SomeArrow (..)
  , someArrow
  , readBack
  , readBackWith

    -- * Simplifying
  , SIMPLIFY
  , Prim
  , unsafePrim
  , prim
  , simplify
  , simplifyWith
  ) where

import Control.Monad (foldM, msum)
import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Constraint, Type)
import Data.List qualified as List
import Data.Map.Strict qualified as M
import Data.Maybe (isJust)
import Data.Ord (comparing)
import Data.Set qualified as Set
import Data.Type.Equality (type (~))
import Data.Universe.Class (Finite (..), Universe (..))
import Unsafe.Coerce (unsafeCoerce)
import Prelude qualified as P

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.FinHask (FINHASK (..), FinHask (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Applicative (Alternative (..))
import Proarrow.Category.Monoidal.Hypergraph (Hypergraph, Sized (..), traceHG)
import Proarrow.Category.Monoidal.Strictified
  ( Fold
  , Strictified (..)
  , concatMany
  , obj1
  , singleton
  , splitMany
  , swap2
  , withIsListOf
  , withObFold
  , type (++)
  )
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..), Kind, OB, Ob', Profunctor, Promonad (..), UN, (//))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (comultS, counitS, mappendS, memptyS)
import Proarrow.Object
  ( KnownListOf (..)
  , ListOf (..)
  , SomeOf (..)
  , appendListOf
  , lengthListOf
  , someOfList
  , withKnownListOf
  , withListOf
  )
import Proarrow.Optic.Iso (DecidableIso (..), withIso)

-- * Sorts

-- | A sort of kind @s@, an object of the category of @s@, known at runtime.
type SomeSort :: Kind -> Type
type SomeSort s = SomeOf (SortOb @s)

-- | The evidence a sort carries: objecthood.
type SortOb :: forall s. s -> Constraint
type SortOb @s = (Ob' :: s -> Constraint)

-- | Whether two sorts are isomorphic.
sameSort :: forall s. (DecidableIso s) => SomeSort s -> SomeSort s -> P.Bool
sameSort = lineUp (byIso @s)

-- | The sorts of the ports of a sorted finite set.
type PortSorts :: forall s. FINHASK -> [s]
type family PortSorts a where
  PortSorts (FH (Port xs)) = xs

-- | The finite sets of ports with sorts of kind @s@, @'FH' (Port xs)@.
type Sorted :: Kind -> OB FINHASK
class (Ob a, a ~ FH (Port (PortSorts @s a)), SortList (PortSorts @s a)) => Sorted s a

instance (Ob a, a ~ FH (Port (PortSorts @s a)), SortList (PortSorts @s a)) => Sorted s a

-- | The sort of a port.
sortOf :: forall s a. (Sorted s a) => UN FH a -> SomeSort s
sortOf = \(Port i) -> table M.! i
  where
    table = M.fromList (P.zip [0 ..] (sortList @s @(PortSorts @s a)))

-- | A list of sorts, each an object known at runtime.
type Sorts :: forall s. [s] -> Type
type Sorts @s = ListOf (SortOb @s)

-- | A list of sorts known at runtime.
type SortList :: forall s. [s] -> Constraint
type SortList xs = KnownListOf SortOb xs

-- | The list of sorts as a value.
sorts :: forall s (xs :: [s]). (SortList xs) => Sorts xs
sorts = listOf

-- | The sorts of the list, one by one.
sortList :: forall s (xs :: [s]). (SortList xs) => [SomeSort s]
sortList = someOfList (sorts @s @xs)

-- | The ports of a list of sorts: one for each position, of the sort at that position.
type Port :: [s] -> Type
newtype Port xs = Port P.Int
  deriving (P.Eq, P.Ord, P.Show)

instance (SortList (xs :: [s])) => Universe (Port xs) where
  universe = P.fmap Port [0 .. lengthListOf (sorts @s @xs) P.- 1]
instance (SortList (xs :: [s])) => Finite (Port xs)

-- | A list of sorts known at runtime as a type-level list.
reifySorts :: forall s r. [SomeSort s] -> (forall (xs :: [s]). (SortList xs) => r) -> r
reifySorts ss k = withListOf ss \ @xs l -> withKnownListOf l (k @xs)

-- | The finite sets whose elements have sorts of kind @s@: a full subcategory of 'FINHASK'.
type SORTED :: Kind -> Kind
type SORTED s = SUBCAT (Sorted s)

-- | No ports.
instance HasInitialObject (SORTED s) where
  type InitialObject @(SORTED s) = SUB (FH (Port ('[] :: [s])))
  initiate = Sub (FinHask M.empty)

-- | The ports of both, those of the second numbered after those of the first.
instance HasBinaryCoproducts (SORTED s) where
  type (||) @(SORTED s) a b = SUB (FH (Port (PortSorts @s (UN SUB a) ++ PortSorts @s (UN SUB b))))
  withObCoprod @a @b r = withKnownListOf (appendListOf (sorts @s @(PortSorts @s (UN SUB a))) (sorts @s @(PortSorts @s (UN SUB b)))) r
  lft @a @b =
    withObCoprod @(SORTED s) @a @b
      (Sub (FinHask (M.fromList [(Port i, Port i) | Port i <- universeF @(Port (PortSorts @s (UN SUB a)))])))
  rgt @a @b =
    withObCoprod @(SORTED s) @a @b
      ( Sub
          ( FinHask
              ( M.fromList
                  [ (Port j, Port (lengthListOf (sorts @s @(PortSorts @s (UN SUB a))) P.+ j))
                  | Port j <- universeF @(Port (PortSorts @s (UN SUB b)))
                  ]
              )
          )
      )
  (|||) @x @_ @y (Sub (FinHask f)) (Sub (FinHask g)) =
    withObCoprod @(SORTED s) @x @y P.$
      Sub
        ( FinHask
            (M.fromList ([(Port i, x) | (Port i, x) <- M.toList f] P.++ [(Port (M.size f P.+ j), x) | (Port j, x) <- M.toList g]))
        )

-- | The pushout of 'FINHASK', whose apex is then renumbered as the ports of the sorts of its
-- elements, each of which comes from one of the two sides.
instance HasPushouts (SORTED s) where
  pushout (Sub @_ @_ @a f) (Sub @_ @_ @b g) k = pushout f g \(FinHask l) (FinHask r) ->
    let
      sortA = sortOf @s @a
      sortB = sortOf @s @b
      nodeSorts = M.fromList ([(p, sortA x) | (x, p) <- M.toList l] P.++ [(p, sortB y) | (y, p) <- M.toList r])
      nodes = M.keys nodeSorts
    in
      reifySorts (M.elems nodeSorts) \ @xs ->
        let renumber = M.fromList (P.zip nodes (P.fmap Port [0 ..]))
        in k (Sub (FinHask @_ @(Port xs) (P.fmap (renumber M.!) l))) (Sub (FinHask (P.fmap (renumber M.!) r)))
  factorPushout (Sub p1) (Sub p2) (Sub k1) (Sub k2) = Sub (factorPushout p1 p2 k1 k2)

-- * Open hypergraphs

-- | A box with a label, attached to nodes of type @n@ by its inputs and its outputs.
type Box :: Type -> Type -> Type
data Box l n = Box {label :: l, inputs :: [n], outputs :: [n]}
  deriving (P.Eq, P.Ord, P.Show, P.Functor)

-- | Labelled boxes on the nodes of a sorted finite set. Two lists of boxes in a different order
-- describe the same hypergraph, which 'isomorphic' takes into account.
type Boxes :: Type -> SORTED s -> Type
data Boxes l c where
  Boxes :: [Box l n] -> Boxes l (SUB (FH n))

instance Functor (Boxes l :: SORTED s -> Type) where
  map (Sub (FinHask m)) (Boxes bs) = Boxes (P.fmap (P.fmap (m M.!)) bs)

-- | No boxes, and the boxes of both sides, the nodes of the second numbered after those of the first.
instance Alternative (Boxes l :: SORTED s -> Type) where
  empty () = Boxes []
  alt @a h (Boxes xs, Boxes ys) =
    map h (Boxes (P.fmap (P.fmap (\(Port i) -> Port i)) xs P.++ P.fmap (P.fmap (\(Port j) -> Port (offset P.+ j))) ys))
    where
      offset = lengthListOf (sorts @s @(PortSorts @s (UN SUB a)))

-- | Open hypergraphs with boxes labelled by @l@ and wires of sorts of kind @s@.
type OPENHG :: Kind -> Type -> Kind
type OPENHG s l = DECCOSPAN (Boxes l :: SORTED s -> Type)

-- | The boundary with a wire for each sort in the list.
type Wires :: forall s l. [s] -> OPENHG s l
type Wires xs = DC (SUB (FH (Port xs)))

-- | The sorts of the wires of a boundary.
type WireSorts :: forall s l. OPENHG s l -> [s]
type WireSorts a = PortSorts (UN SUB (UN DC a))

-- | One box with the given label, its inputs the wires of @as@ and its outputs those of @bs@: a
-- generator of the free hypergraph category.
box :: forall {s} l (as :: [s]) (bs :: [s]). (SortList as, SortList bs) => l -> Wires as ~> (Wires bs :: OPENHG s l)
box x =
  withObCoprod @(SORTED s) @(SUB (FH (Port as))) @(SUB (FH (Port bs)))
    ( DecCospan
        (lft @_ @(SUB (FH (Port as))) @(SUB (FH (Port bs))))
        (rgt @_ @(SUB (FH (Port as))) @(SUB (FH (Port bs))))
        (Boxes [Box x (P.take na ports) (P.drop na ports)])
    )
  where
    na = lengthListOf (sorts @s @as)
    ports = P.fmap Port [0 .. na P.+ lengthListOf (sorts @s @bs) P.- 1]

-- | The open hypergraph with nodes of the given sorts, the wires of @as@ and of @bs@ attached to
-- the given nodes, and boxes on the given nodes, numbered from 0. Fails with a message unless every
-- wire has a sort isomorphic to that of its node and every node exists.
openHypergraph
  :: forall {s} l (as :: [s]) (bs :: [s])
   . (SortList as, SortList bs, DecidableIso s)
  => [SomeSort s]
  -> [P.Int]
  -> [P.Int]
  -> [Box l P.Int]
  -> P.Either P.String (Wires as ~> (Wires bs :: OPENHG s l))
openHypergraph nodeSorts ins outs boxList
  | P.length ins P./= lengthListOf (sorts @s @as) P.|| P.length outs P./= lengthListOf (sorts @s @bs) =
      P.Left "openHypergraph: a boundary has a different number of wires than its sorts"
  | P.any
      (`M.notMember` sortAt)
      (ins P.++ outs P.++ P.concat [inputs bx P.++ outputs bx | bx <- boxList]) =
      P.Left "openHypergraph: a wire or box is attached to a node that does not exist"
  | P.not
      ( lineUpAll byIso (P.fmap (sortAt M.!) ins) (sortList @s @as)
          P.&& lineUpAll byIso (P.fmap (sortAt M.!) outs) (sortList @s @bs)
      ) =
      P.Left "openHypergraph: a wire does not have the sort of its node"
  | P.otherwise = P.Right (unsafeOpenHypergraph nodeSorts ins outs boxList)
  where
    sortAt = M.fromList (P.zip [0 ..] nodeSorts)

-- | 'openHypergraph' without its checks: the boundaries must have as many wires as their sorts,
-- every wire and box must be attached to nodes that exist, and every wire must have the sort of its
-- node. Only for hypergraphs that satisfy this by construction, such as those that 'simplify' is
-- given, which trusts the sorts to be equal.
unsafeOpenHypergraph
  :: forall {s} l (as :: [s]) (bs :: [s])
   . (SortList as, SortList bs)
  => [SomeSort s]
  -> [P.Int]
  -> [P.Int]
  -> [Box l P.Int]
  -> Wires as ~> (Wires bs :: OPENHG s l)
unsafeOpenHypergraph nodeSorts ins outs boxList = reifySorts nodeSorts \ @ns ->
  DecCospan
    (Sub (FinHask (M.fromList (P.zip universeF (P.fmap (Port @_ @ns) ins)))))
    (Sub (FinHask (M.fromList (P.zip universeF (P.fmap (Port @_ @ns) outs)))))
    (Boxes (P.fmap (P.fmap Port) boxList))

-- | Whether two open hypergraphs differ only in the names of their nodes, the order of their boxes
-- and their sorts up to isomorphism: a bijection between the nodes that keeps their sorts, agrees
-- with both boundaries and takes the boxes of one to those of the other.
isomorphic :: forall {s} l a b. (P.Eq l, DecidableIso s) => (a :: OPENHG s l) ~> b -> a ~> b -> P.Bool
isomorphic
  (DecCospan @c1 (Sub (FinHask l1)) (Sub (FinHask r1)) (Boxes bs1))
  (DecCospan @c2 (Sub (FinHask l2)) (Sub (FinHask r2)) (Boxes bs2)) =
    -- the nodes that nothing is attached to can be matched up exactly when this holds
    sameBag sameSort (P.fmap sort1 nodes1) (P.fmap sort2 nodes2)
      P.&& sameBag (P.==) (P.fmap shape bs1) (P.fmap shape bs2)
      P.&& isJust
        (extendAll (M.empty, M.empty) (P.zip (M.elems l1) (M.elems l2) P.++ P.zip (M.elems r1) (M.elems r2)) P.>>= boxes bs1 bs2)
    where
      nodes1 = universeF @(UN FH (UN SUB c1))
      nodes2 = universeF @(UN FH (UN SUB c2))
      sort1 = sortOf @s @(UN SUB c1)
      sort2 = sortOf @s @(UN SUB c2)
      shape (Box x i o) = (x, P.length i, P.length o)
      -- the same elements, counted with multiplicity
      sameBag _ [] ys = P.null ys
      sameBag eq (x : xs) ys = case List.break (eq x) ys of
        (_, []) -> P.False
        (before, _ : after) -> sameBag eq xs (before P.++ after)
      boxes [] _ m = P.Just m
      boxes (x : xs) ys m = msum [match x y m P.>>= boxes xs rest | (y, rest) <- picks ys]
      match (Box lx ix ox) (Box ly iy oy) m
        | lx P.== ly P.&& P.length ix P.== P.length iy P.&& P.length ox P.== P.length oy =
            extendAll m (P.zip ix iy P.++ P.zip ox oy)
        | P.otherwise = P.Nothing
      extendAll = foldM (P.flip extend)
      extend (x, y) (fwd, bwd)
        | P.not (sameSort (sort1 x) (sort2 y)) = P.Nothing
        | P.otherwise = case (M.lookup x fwd, M.lookup y bwd) of
            (P.Nothing, P.Nothing) -> P.Just (M.insert x y fwd, M.insert y x bwd)
            (P.Just y', P.Just x') | y' P.== y P.&& x' P.== x -> P.Just (fwd, bwd)
            _ -> P.Nothing
      picks :: [x] -> [(x, [x])]
      picks xs = [(x, before P.++ after) | (before, x : after) <- P.zip (List.inits xs) (List.tails xs)]

-- * Read-back

-- | An arrow of the strictified category of @s@ whose lists of sorts are known at runtime, such as
-- the interpretation of a box.
type SomeArrow :: Kind -> Type
data SomeArrow s where
  SomeArrow :: forall {s} (as :: [s]) bs. Sorts as -> Sorts bs -> as ~> bs -> SomeArrow s

-- | An arrow as one whose sorts are known at runtime.
someArrow :: forall {s} (as :: [s]) bs. (SortList as, SortList bs) => as ~> bs -> SomeArrow s
someArrow = SomeArrow (sorts @s @as) (sorts @s @bs)

-- | The term of a hypergraph category that an open hypergraph stands for, given an arrow for each
-- label: 'readBackWith' with the sizes from 'Sized'.
readBack
  :: forall {s} l a b
   . (Hypergraph s, Sized s, DecidableIso s)
  => (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
readBack = readBackWith (sizeFromSized @s)

-- | The term of a hypergraph category that an open hypergraph stands for, given the size of each
-- sort and an arrow for each label. A box first merges its own wires of one node and discards those
-- that nothing else needs, and a node is merged as soon as nothing still to come needs it. The order
-- is numpy's greedy one, which takes the contraction whose result grows least, its size less the
-- sizes of the two parts. The boxes without inputs are contracted with each other first, as a tree
-- of pairs that share a node, so a network of tensors is read back as its contraction tree. The
-- pieces and the other boxes then follow the flow of their wires one at a time, with between two
-- boxes one spider per node. A node that a box uses no later than a box makes it is fed back with
-- a trace, which only a cyclic hypergraph needs. Fails with a message when an arrow does not fit
-- its box. An arrow whose sorts are isomorphic to those of its box is moved along the
-- isomorphisms.
readBackWith
  :: forall {s} l a b
   . (Hypergraph s, DecidableIso s)
  => (SomeSort s -> P.Int)
  -> (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
readBackWith = readBackAligned (byIso @s)

-- | The read-back, with the sorts lined up by the given alignment.
readBackAligned
  :: forall {s} l a b
   . (Hypergraph s)
  => Align s
  -> (SomeSort s -> P.Int)
  -> (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
readBackAligned al sizeFn interp hg@(DecCospan @c (Sub (FinHask legIn)) (Sub (FinHask legOut)) (Boxes boxList)) =
  hg // do
    arrows0 <- M.fromList P.<$> P.traverse interpBox labelled
    let arrows = M.union arrows0 (M.fromList [(j, pieceArrow al nodeSort arrows0 t) | (j, t) <- merged])
    P.pure P.$ withListOf (P.fmap (nodeSort P.. KN) (feedback lt)) \fb ->
      let insS = sorts @s @(WireSorts a)
          outsS = sorts @s @(WireSorts b)
          start = appendListOf fb insS
          (bundle, body) =
            P.foldl
              (step al nodeSort lt arrows)
              (P.fmap KN (feedback lt P.++ shapeIns shape), Built start Same)
              (P.zip [1 ..] order)
          final =
            transition
              al
              nodeSort
              (isolated shape boxes0)
              bundle
              (P.fmap KL (feedback lt) P.++ P.fmap (outKey lt) (shapeOuts shape))
              body
      in case final of
           Built ys whole -> case alignSteps al ys (appendListOf fb outsS) of
             P.Just to -> traceSorts fb insS outsS (arrowOf ys to . arrowOf start whole)
             P.Nothing -> P.error "readBack: the boundaries were planned with other sorts"
  where
    nodes = universeF @(UN FH (UN SUB c))
    index = M.fromList (P.zip nodes [0 :: P.Int ..])
    sortC = sortOf @s @(UN SUB c)
    sortAt = M.fromList [(index M.! n, sortC n) | n <- nodes]
    nodeSort k = sortAt M.! keyNode k
    labelled = P.zip [0 :: P.Int ..] [P.fmap (index M.!) bx | bx <- boxList]
    shape =
      Shape
        { shapeNodes = M.elems index
        , shapeIns = P.fmap (index M.!) (M.elems legIn)
        , shapeOuts = P.fmap (index M.!) (M.elems legOut)
        }
    boxes0 = [(i, bx{label = ()}) | (i, bx) <- labelled]
    size ns = P.product [P.fromIntegral (sizeFn (sortAt M.! n)) :: P.Double | n <- Set.toList ns]
    (boxesIx, merged) = pathBoxes boxes0 (contractStates size shape boxes0)
    order = schedule size shape boxesIx
    lt = lifetimes shape boxesIx order
    interpBox (i, Box x is os) = case interp x of
      arr@(SomeArrow xs ys _)
        | lineUpAll al (someOfList xs) (nodeSorts is) P.&& lineUpAll al (someOfList ys) (nodeSorts os) -> P.Right (i, arr)
        | P.otherwise -> P.Left "readBack: the arrow of a label does not have the sorts of its box"
    nodeSorts = P.fmap (nodeSort P.. KN)

-- ** Planning

-- | The nodes of an open hypergraph, numbered from 0, and its boundaries.
data Shape = Shape {shapeNodes :: [P.Int], shapeIns :: [P.Int], shapeOuts :: [P.Int]}

-- | A numbered box.
type Ix = (P.Int, Box () P.Int)

touches :: Ix -> Set.Set P.Int
touches (_, bx) = Set.fromList (inputs bx P.++ outputs bx)

without :: Ix -> [Ix] -> [Ix]
without bx = P.filter (\b -> P.fst b P./= P.fst bx)

-- | The nodes that the given boxes or the outputs need.
neededBy :: Shape -> [Ix] -> Set.Set P.Int
neededBy sh rest = Set.unions (Set.fromList (shapeOuts sh) : [touches b | b <- rest])

-- | The nodes that are open once the placed nodes are in, with the given boxes still to come.
openAfter :: Shape -> Set.Set P.Int -> [Ix] -> Set.Set P.Int
openAfter sh placed rest = Set.intersection (Set.union (Set.fromList (shapeIns sh)) placed) (neededBy sh rest)

-- | What is left of a box on its own, among the given boxes: its nodes that the boundary or another
-- box needs.
alone :: Shape -> [Ix] -> Ix -> Set.Set P.Int
alone sh bxs bx = Set.intersection (touches bx) (Set.union (Set.fromList (shapeIns sh)) (neededBy sh (without bx bxs)))

-- | How much a contraction makes the result grow: the size of the result less the sizes of the two
-- parts, which numpy's greedy order keeps smallest.
gain :: (Set.Set P.Int -> P.Double) -> Set.Set P.Int -> Set.Set P.Int -> Set.Set P.Int -> P.Double
gain size whole a b = size whole P.- size a P.- size b

-- | Some of the boxes without inputs, contracted as a tree, with how many of them touch each node and
-- the nodes something outside them needs.
data Piece = Piece {pieceTree :: Tree, pieceCounts :: M.Map P.Int P.Int, pieceOpen :: Set.Set P.Int}

-- | The boxes without inputs contracted with each other as a tree, in numpy's greedy order: the pair
-- that shares a node and whose result grows least, until no two share a node.
contractStates :: (Set.Set P.Int -> P.Double) -> Shape -> [Ix] -> [Piece]
contractStates size sh bxs = contract [leaf b | b@(_, bx) <- bxs, P.null (inputs bx)]
  where
    -- how many boxes and boundaries touch each node; a piece needs to keep a node that they touch
    -- more often than its own boxes do
    total =
      M.fromListWith
        (P.+)
        ([(n, 1) | b <- bxs, n <- Set.toList (touches b)] P.++ [(n, 1) | n <- nubOrd (shapeIns sh P.++ shapeOuts sh)])
    openIn counts = Set.fromList [n | (n, c) <- M.toList counts, c P.< total M.! n]
    keysIn open made = [k | k <- nubOrd made, keyNode k `Set.member` open]
    leaf b@(i, bx) =
      let counts = M.fromList [(n, 1) | n <- Set.toList (touches b)]
          open = openIn counts
      in Piece (Leaf i (P.fmap KN (outputs bx)) (keysIn open (P.fmap KN (outputs bx)))) counts open
    merge a b =
      let counts = M.unionWith (P.+) (pieceCounts a) (pieceCounts b)
          open = openIn counts
      in Piece (Merge (pieceTree a) (pieceTree b) (keysIn open (treeKeys (pieceTree a) P.++ treeKeys (pieceTree b)))) counts open
    contract ps =
      case [ (gain size (pieceOpen ab) (pieceOpen a) (pieceOpen b), a, b, ab)
           | a : rest <- List.tails ps
           , b <- rest
           , P.not (Set.disjoint (pieceOpen a) (pieceOpen b))
           , let ab = merge a b
           ] of
        [] -> ps
        cs ->
          let (_, a, b, ab) = List.minimumBy (comparing (\(c, _, _, _) -> c)) cs
          in contract [if pieceTree q P.== pieceTree a then ab else q | q <- ps, pieceTree q P./= pieceTree b]

-- | The boxes read back along a path: those with inputs, the states left on their own, and one box
-- for each piece of more than one state, numbered after the boxes, with those pieces.
pathBoxes :: [Ix] -> [Piece] -> ([Ix], [(P.Int, Tree)])
pathBoxes bxs pieces =
  ( [b | b@(i, bx) <- bxs, P.not (P.null (inputs bx)) P.|| i `P.elem` alone']
      P.++ [(j, Box () [] (P.fmap keyNode (treeKeys t))) | (j, t) <- merged]
  , merged
  )
  where
    alone' = [i | Piece{pieceTree = Leaf i _ _} <- pieces]
    merged = [(j, t) | (j, Piece{pieceTree = t@Merge{}}) <- P.zip [P.length bxs ..] pieces]

-- | The boxes one at a time, in numpy's greedy order: of the boxes whose inputs are made, the one
-- whose contraction with the open nodes costs least, or the first of the cheapest pair while no node
-- is open; a box on a cycle when no box is ready.
schedule :: (Set.Set P.Int -> P.Double) -> Shape -> [Ix] -> [Ix]
schedule size sh bxs = go Set.empty bxs
  where
    go _ [] = []
    go placed remaining =
      let open = openAfter sh placed remaining
          after bx = openAfter sh (Set.union placed (touches bx)) (without bx remaining)
          cost bx = gain size (after bx) open (alone sh bxs bx)
          pairCost (x, y) =
            gain
              size
              (openAfter sh (Set.union placed (Set.union (touches x) (touches y))) (without y (without x remaining)))
              (alone sh bxs x)
              (alone sh bxs y)
          next
            | Set.null open
            , _ : _ : _ <- remaining =
                P.fst (List.minimumBy (comparing pairCost) [(x, y) | x <- candidates remaining, y <- candidates (without x remaining)])
            | P.otherwise = List.minimumBy (comparing cost) (candidates remaining)
      in next : go (Set.union placed (touches next)) (without next remaining)
    candidates remaining = case [bx | bx <- remaining, P.not (P.any (dependsOn bx) remaining)] of
      [] -> P.take 1 remaining
      ready -> ready
    -- a box depends on another when it uses a node the other makes
    dependsOn (i, bi) (j, bj) = i P./= j P.&& P.any (`P.elem` outputs bj) (inputs bi)

-- | When the wires of the read-back are needed, for the boxes in the given order.
data Lifetimes = Lifetimes
  { feedback :: [P.Int]
  -- ^ the nodes that a box uses no later than a box makes them, fed back with a trace
  , outKey :: P.Int -> Key
  -- ^ the wire that a box makes of a node
  , live :: P.Int -> Key -> P.Bool
  -- ^ whether a wire is needed after the given step: a later box uses it or makes another part of
  -- it, or it is an output; what boxes make of a node fed back goes on its other wire, to the end
  }

lifetimes :: Shape -> [Ix] -> [Ix] -> Lifetimes
lifetimes sh bxs order = Lifetimes{feedback = fb, outKey = key, live = alive}
  where
    layerOf = M.fromList (P.zip (P.fmap P.fst order) [1 :: P.Int ..])
    madeAt = M.fromListWith (P.++) [(n, [layerOf M.! i]) | (i, bx) <- bxs, n <- outputs bx]
    usedAt = M.fromListWith (P.++) [(n, [layerOf M.! i]) | (i, bx) <- bxs, n <- inputs bx]
    layersOf n m = M.findWithDefault [] n m
    fb = [n | n <- shapeNodes sh, P.or [mk P.>= u | u <- layersOf n usedAt, mk <- layersOf n madeAt]]
    key n = if n `P.elem` fb then KL n else KN n
    alive t (KN n)
      | n `P.elem` fb = P.any (P.> t) (layersOf n usedAt)
      | P.otherwise = P.any (P.> t) (layersOf n usedAt P.++ layersOf n madeAt) P.|| n `P.elem` shapeOuts sh
    alive _ (KL _) = P.True

-- | The nodes attached to none of the given boxes and to no boundary: closed loops, spiders without
-- legs.
isolated :: Shape -> [Ix] -> [Key]
isolated sh bxs = [KN n | n <- shapeNodes sh, n `Set.notMember` attached]
  where
    attached = Set.fromList (shapeIns sh P.++ shapeOuts sh P.++ P.concat [inputs bx P.++ outputs bx | (_, bx) <- bxs])

-- ** Building

-- | The term of a piece: a state with its own wires of one node merged and those nothing else needs
-- discarded, or two halves side by side with the nodes only they need merged away.
pieceArrow
  :: forall s. (Hypergraph s) => Align s -> (Key -> SomeSort s) -> M.Map P.Int (SomeArrow s) -> Tree -> SomeArrow s
pieceArrow al nodeSort arrows0 t0 = case go t0 of
  Built ys f -> SomeArrow Nil ys (arrowOf Nil f)
  where
    go :: Tree -> Built ('[] :: [s])
    go t = transition al nodeSort [] (treeMade t) (treeKeys t) (body t)
    body (Leaf i _ _) = boxThen al (arrows0 M.! i) Nil
    body (Merge l r _) = beside Nil (go l) Nil (go r)

-- | One box placed after the wires that go past it, between the spiders before and after it.
step
  :: forall s (xs :: [s])
   . (Hypergraph s)
  => Align s
  -> (Key -> SomeSort s)
  -> Lifetimes
  -> M.Map P.Int (SomeArrow s)
  -> ([Key], Built xs)
  -> (P.Int, Ix)
  -> ([Key], Built xs)
step al nodeSort lt arrows (bundle, body) (t, (i, bx)) =
  let need = P.fmap KN (inputs bx)
      made = P.fmap (outKey lt) (outputs bx)
      -- a wire goes past the box when it is needed after it or is merged with a wire across it:
      -- the carried wires, and what is left of the box, its wires of one node merged
      carry = [k | k <- nubOrd (bundle P.++ need), live lt t k P.|| k `P.elem` made]
      kept = [k | k <- nubOrd made, live lt t k P.|| k `P.elem` carry]
      -- the box goes after the carried wires, next to the wires it is merged with later
      run :: forall (ws :: [s]). Sorts ws -> Built ws
      run ws = splitSorts (P.length carry) ws \pre post ->
        beside pre (Built pre Same) post (transition al nodeSort [] made kept (boxThen al (arrows M.! i) post))
  in ( carry P.++ kept
     , run `afterBuilt` transition al nodeSort [] bundle (carry P.++ need) body
     )

-- | What is built so far followed by one spider per wire kind, also for the given kinds without
-- wires, between permutations that group the wires. Each step is composed onto what is built so far
-- by itself, so that in a category of matrices a state is only ever multiplied by one step.
transition
  :: forall s (xs :: [s])
   . (Hypergraph s) => Align s -> (Key -> SomeSort s) -> [Key] -> [Key] -> [Key] -> Built xs -> Built xs
transition al nodeSort extra from to built =
  let present = nubOrd (from P.++ to)
      kinds = groupOrder from to present P.++ [k | k <- extra, k `P.notElem` present]
      count k ks = P.length (P.filter (P.== k) ks)
      identity = P.all (\k -> count k from P.== 1 P.&& count k to P.== 1) kinds
      spiders :: forall (ws :: [s]). Sorts ws -> Built ws
      spiders ws
        | identity = Built ws Same
        | P.otherwise = spidersThen al [(nodeSort k, count k from, count k to) | k <- kinds] ws
  in permuteThen (inverse (positionsIn kinds to)) (spiders `afterBuilt` permuteThen (positionsIn kinds from) built)
  where
    inverse p = P.fmap P.snd (List.sort (P.zip p [0 :: P.Int ..]))

-- | The positions of the wires in the order that groups them by kind.
positionsIn :: [Key] -> [Key] -> [P.Int]
positionsIn kinds ks = [i | k <- kinds, i <- [j | (j, k') <- P.zip [0 :: P.Int ..] ks, k' P.== k]]

-- | The order of the kinds that needs the fewest swaps, each weighed by the number of wires it
-- crosses: every order for a few kinds, else by the average position of their wires. The swaps
-- between two kinds depend only on which of them goes first.
groupOrder :: [Key] -> [Key] -> [Key] -> [Key]
groupOrder from to present
  | P.length present P.<= 6 = List.minimumBy (comparing cost) (List.permutations present)
  | P.otherwise = List.sortOn average present
  where
    crossings ks = M.fromListWith (P.+) [((a, b), 1 :: P.Int) | (j, a) <- P.zip [0 :: P.Int ..] ks, b <- P.take j ks, a P./= b]
    weighed = M.unionWith (P.+) (P.fmap (P.* P.length from) (crossings from)) (P.fmap (P.* P.length to) (crossings to))
    -- each pair of kinds in the wrong order costs its wires that cross
    cost kinds = P.sum [M.findWithDefault 0 (a, b) weighed | (j, b) <- P.zip [0 :: P.Int ..] kinds, a <- P.take j kinds]
    average k =
      let is = [i | (i, k') <- P.zip [0 :: P.Int ..] (from P.++ to), k' P.== k]
      in P.fromIntegral (P.sum is) P./ (P.fromIntegral (P.length is) :: P.Double)

-- * Simplifying

-- | Open hypergraphs whose boxes are arrows of @k@: the category to run a term of a hypergraph
-- category in, with the arrows it uses made boxes by 'prim', to 'simplify' it.
type SIMPLIFY :: Kind -> Kind
type SIMPLIFY k = OPENHG k (Prim k)

-- | The label of a box of 'SIMPLIFY': the arrow the box was made from, whose sorts are those of the
-- box. Made only by 'prim', so 'simplify' can trust the sorts. Taking a label out of one hypergraph
-- and attaching it to other nodes with 'openHypergraph' breaks that trust.
type Prim :: Kind -> Type
newtype Prim k = Prim (SomeArrow k)

-- | An arrow of @k@ between lists of objects as one box.
prim
  :: forall {k} (as :: [k]) bs. (SortList as, SortList bs) => as ~> bs -> Wires as ~> (Wires bs :: SIMPLIFY k)
prim f = box (Prim (someArrow f))

-- | An arrow as the label of a box with any sorts. Only for boxes whose sorts are equal to the
-- arrow's by construction, as for 'unsafeOpenHypergraph'.
unsafePrim :: SomeArrow k -> Prim k
unsafePrim = Prim

-- | The term of @k@ that a term run in 'SIMPLIFY' stands for: its read-back, with each box the
-- arrow it was made from, and the sizes from 'Sized'.
simplify :: forall {k} a b. (Hypergraph k, Sized k) => (a :: SIMPLIFY k) ~> b -> WireSorts a ~> WireSorts b
simplify = simplifyWith (sizeFromSized @k)

-- | 'simplify' with the given sizes. The sorts of a box are those of its arrow, so they need not be
-- compared.
simplifyWith
  :: forall {k} a b. (Hypergraph k) => (SomeSort k -> P.Int) -> (a :: SIMPLIFY k) ~> b -> WireSorts a ~> WireSorts b
simplifyWith sizeFn t = case readBackAligned trusted sizeFn (\(Prim a) -> a) t of
  P.Right r -> r
  P.Left e -> P.error e

-- | The size of a sort, from 'Sized'.
sizeFromSized :: forall s. (Sized s) => SomeSort s -> P.Int
sizeFromSized (Some @x) = sizeOf @s @x

-- | A way to line up a wire of one sort with one of another: nothing to do when they are equal, an
-- arrow along their isomorphism otherwise, or nothing when they cannot be.
type Align :: Kind -> Type
type Align s = forall (x :: s) (y :: s). (Ob x, Ob y) => P.Maybe (Step '[x] '[y])

-- | Sorts lined up along an isomorphism found by 'DecidableIso'.
byIso :: forall s. (DecidableIso s) => Align s
byIso @_ @x @y = P.fmap (\o -> withIso @Profunctor o \f _ -> Arrow (singleton f)) (isoOf @s @Profunctor @x @y)

-- | Sorts taken to be equal, as they are when they come from the same arrow.
trusted :: forall s. Align s
trusted @_ @x @y = P.Just (unsafeCoerce (Same :: Step '[x] '[x]) :: Step '[x] '[y])

-- | The states contracted into one piece, as a tree of box numbers, each with the wires it ends in:
-- its open nodes, each once, in the order their wires come in. A leaf also has the wires of its box.
data Tree = Leaf P.Int [Key] [Key] | Merge Tree Tree [Key]
  deriving (P.Eq)

treeKeys :: Tree -> [Key]
treeKeys (Leaf _ _ ks) = ks
treeKeys (Merge _ _ ks) = ks

-- | The wires that come into the last step of a piece.
treeMade :: Tree -> [Key]
treeMade (Leaf _ made _) = made
treeMade (Merge l r _) = treeKeys l P.++ treeKeys r

-- | The wires of the read-back: a node, and the part of a node that cyclic boxes make, which is fed
-- back to the node.
data Key = KN P.Int | KL P.Int
  deriving (P.Eq, P.Ord)

keyNode :: Key -> P.Int
keyNode (KN n) = n
keyNode (KL n) = n

-- | An arrow from @xs@ to sorts known at runtime, or none yet.
type Step :: forall s. [s] -> [s] -> Type
data Step xs ys where
  Same :: Step xs xs
  Arrow :: xs ~> ys -> Step xs ys

-- | What is built so far from @xs@: the sorts it ends in and how it gets there.
type Built :: forall s. [s] -> Type
data Built xs where
  Built :: Sorts ys -> Step xs ys -> Built xs

-- | The next piece, built from the sorts the previous one ends in.
afterBuilt :: forall {s} (xs :: [s]). (Monoidal s) => (forall (ys :: [s]). Sorts ys -> Built ys) -> Built xs -> Built xs
afterBuilt k (Built ys f) = case k ys of
  Built zs g -> Built zs (compose g f)
  where
    compose Same h = h
    compose h Same = h
    compose (Arrow q) (Arrow p) = Arrow (q . p)

arrowOf :: (Monoidal s) => Sorts (xs :: [s]) -> Step xs ys -> xs ~> ys
arrowOf xs Same = withIsListOf xs id
arrowOf _ (Arrow f) = f

-- | Two built pieces side by side.
beside :: (Monoidal s) => Sorts (xs :: [s]) -> Built xs -> Sorts xs' -> Built xs' -> Built (xs ++ xs')
beside xs (Built ys f) xs' (Built ys' g) = Built (appendListOf ys ys') (besideStep xs f xs' g)

-- | Two steps side by side.
besideStep
  :: (Monoidal s) => Sorts (xs :: [s]) -> Step xs ys -> Sorts xs' -> Step xs' ys' -> Step (xs ++ xs') (ys ++ ys')
besideStep _ Same _ Same = Same
besideStep xs f xs' g = Arrow (arrowOf xs f ** arrowOf xs' g)

-- | The list split after its first @n@ sorts.
splitSorts :: P.Int -> Sorts xs -> (forall pre post. (xs ~ (pre ++ post)) => Sorts pre -> Sorts post -> r) -> r
splitSorts 0 xs k = k Nil xs
splitSorts n (Cons @x rest) k = splitSorts (n P.- 1) rest \pre post -> k (Cons @x pre) post
splitSorts _ Nil _ = P.error "readBack: a split beyond the wires was planned"

-- | Whether two sorts can be lined up.
lineUp :: forall s. Align s -> SomeSort s -> SomeSort s -> P.Bool
lineUp al (Some @x) (Some @y) = isJust (al @x @y)

-- | Whether two lists of sorts can be lined up, one by one.
lineUpAll :: forall s. Align s -> [SomeSort s] -> [SomeSort s] -> P.Bool
lineUpAll al xs ys = P.length xs P.== P.length ys P.&& P.and (P.zipWith (lineUp al) xs ys)

-- | Wires of the first sorts lined up with the second, one at a time.
alignSteps :: (Monoidal s) => Align s -> Sorts (xs :: [s]) -> Sorts ys -> P.Maybe (Step xs ys)
alignSteps _ Nil Nil = P.Just Same
alignSteps al (Cons @x xs) (Cons @y ys) = do
  a <- al @x @y
  rest <- alignSteps al xs ys
  P.pure (besideStep (single @x) a xs rest)
alignSteps _ _ _ = P.Nothing

single :: forall {s} (x :: s). (Ob' x) => Sorts '[x]
single = Cons @x Nil

-- | The box on the first wires, and the rest of the wires unchanged.
boxThen :: (Monoidal s) => Align s -> SomeArrow s -> Sorts (xs :: [s]) -> Built xs
boxThen al (SomeArrow as bs f) xs = splitSorts (lengthListOf as) xs \pre post -> case alignSteps al pre as of
  P.Just into -> beside pre (Built bs (Arrow (f . arrowOf pre into))) post (Built post Same)
  P.Nothing -> P.error "readBack: a box was planned on wires of other sorts"

-- | What is built so far followed by its wires in the order that @p@ lists them, as adjacent swaps
-- composed one at a time: the wire at position @j@ of the result is wire @p !! j@ before.
permuteThen :: (Hypergraph s) => [P.Int] -> Built (xs :: [s]) -> Built xs
permuteThen p built0 = P.foldl (\built i -> swapThen i `afterBuilt` built) built0 (P.reverse (bubble p []))
  where
    -- the positions of the adjacent swaps that sort @p@
    bubble ps acc = case [i | (i, (a, b)) <- P.zip [0 ..] (P.zip ps (P.drop 1 ps)), a P.> b] of
      [] -> P.reverse acc
      i : _ -> bubble (P.take i ps P.++ [ps P.!! (i P.+ 1), ps P.!! i] P.++ P.drop (i P.+ 2) ps) (i : acc)

-- | The swap of the wires at positions @i@ and @i + 1@.
swapThen :: (Hypergraph s) => P.Int -> Sorts (xs :: [s]) -> Built xs
swapThen 0 (Cons @x (Cons @y rest)) = Built (Cons @y (Cons @x rest)) (Arrow (swap2 @x @y ** withIsListOf rest id))
swapThen i (Cons @x rest) = case swapThen (i P.- 1) rest of
  Built ys f -> Built (Cons @x ys) (Arrow (obj1 @x ** arrowOf rest f))
swapThen _ Nil = P.error "readBack: a swap beyond the wires was planned"

-- | For each sort, a spider from the given number of wires to the given number.
spidersThen :: (Hypergraph s) => Align s -> [(SomeSort s, P.Int, P.Int)] -> Sorts (xs :: [s]) -> Built xs
spidersThen _ [] Nil = Built Nil Same
spidersThen _ [] _ = P.error "readBack: wires without a spider were planned"
spidersThen al ((x, c, m) : rest) xs = splitSorts c xs \pre post -> beside pre (spider al x c m pre) post (spidersThen al rest post)

-- | The spider of a sort from @c@ wires to @m@: merging all of them, then copying the result.
spider :: (Hypergraph s) => Align s -> SomeSort s -> P.Int -> P.Int -> Sorts (pre :: [s]) -> Built pre
spider al (Some @x) c m pre
  | c P.== 1 P.&& m P.== 1 = Built pre Same
  | P.otherwise = case copies @x m of Built ys f -> Built ys (Arrow (arrowOf (single @x) f . merges @x al pre))

-- | All the wires merged into one of sort @x@, each lined up with it first, or the unit of @x@ when
-- there are none.
merges :: forall {s} (x :: s) pre. (Hypergraph s, Ob x) => Align s -> Sorts pre -> pre ~> '[x]
merges _ Nil = memptyS @x
merges al (Cons @y Nil) = toX @y al
merges al (Cons @y rest@Cons{}) = mappendS @x . (toX @y al ** merges @x al rest)

toX :: forall {s} y (x :: s). (Monoidal s, Ob x, Ob y) => Align s -> '[y] ~> '[x]
toX al = case al @y @x of
  P.Just a -> arrowOf (single @y) a
  P.Nothing -> P.error "readBack: a spider was planned on wires of other sorts"

-- | One wire of sort @x@ copied to @m@, or discarded when @m@ is 0.
copies :: forall {s} (x :: s). (Hypergraph s, Ob x) => P.Int -> Built '[x]
copies 0 = Built Nil (Arrow (counitS @x))
copies 1 = Built (single @x) Same
copies 2 = Built (Cons @x (single @x)) (Arrow (comultS @x))
copies m = case copies @x (m P.- 1) of
  Built ys f -> Built (Cons @x ys) (Arrow ((obj1 @x ** arrowOf (single @x) f) . comultS @x))

-- | The trace over the first wires, @us@, which feeds their outputs back to their inputs.
traceSorts
  :: forall {s} (us :: [s]) xs ys
   . (Hypergraph s)
  => Sorts us
  -> Sorts xs
  -> Sorts ys
  -> (us ++ xs) ~> (us ++ ys)
  -> xs ~> ys
traceSorts Nil _ _ f = f
traceSorts us xs ys f =
  withIsListOf us P.$
    withIsListOf xs P.$
      withIsListOf ys P.$
        withObFold @us P.$
          withObFold @xs P.$
            withObFold @ys P.$
              splitMany @ys
                . Str
                  ( traceHG @(Fold us) @(Fold xs) @(Fold ys)
                      (unStr ((concatMany @us ** concatMany @ys) . f . (splitMany @us ** splitMany @xs)))
                  )
                . concatMany @xs
