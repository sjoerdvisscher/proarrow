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
  , SomeHypergraph (..)
  , substitute
  , substituteWith
  , unsafeSubstituteWith
  , isomorphic
  , sameSort

    -- * Read-back
  , SomeArrow (..)
  , someArrow
  , readBack
  , Wiring
  , permutations
  , copyDiscard
  , frobenius
  , frobeniusWith
  , tracedWith
  , layered

    -- * Simplifying
  , SIMPLIFY
  , Prim
  , unsafePrim
  , prim
  , simplify
  , simplifyHypergraph
  , simplifyFlat
  ) where

import Control.Monad (foldM, msum)
import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Constraint, Type)
import Data.List qualified as List
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Ord (comparing)
import Data.Set qualified as Set
import Data.Type.Equality (type (~))
import Data.Universe.Class (Finite (..), Universe (..))
import Unsafe.Coerce (unsafeCoerce)
import Prelude qualified as P

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.FinHask (FINHASK (..), FinHask (..), unionFind)
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..), SymMonoidal, Tensor, type (**))
import Proarrow.Category.Monoidal.Applicative (Alternative (..))
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscard)
import Proarrow.Category.Monoidal.Hypergraph (Frobenius, Hypergraph, Sized (..), cupS, traceHG)
import Proarrow.Category.Monoidal.Strength (Costrong (..), TracedMonoidal)
import Proarrow.Category.Monoidal.Strictified
  ( Fold
  , Strictified (..)
  , concatMany
  , obj1
  , singleton
  , splitMany
  , swap2
  , withIsListOf
  , type (++)
  )
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..), Hom, Kind, OB, Ob', Profunctor, Promonad (..), UN, obj, (//))
import Proarrow.Functor (Functor (..))
import Proarrow.Monoid (CocommutativeComonoid, Supplies, comultS, counitS, mappendS, memptyS)
import Proarrow.Object
  ( KnownListOf (..)
  , ListOf (..)
  , SomeOf (..)
  , appendListOf
  , lengthListOf
  , someOfList
  , withKnownAppend
  , withKnownListOf
  , withListOf
  , pattern Objs
  )
import Proarrow.Optic.Iso (DecidableIso (..), withIso)
import Proarrow.Tools.ContractionOrder (Plan (..), planContraction)

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
  withObCoprod @a @b r = withKnownAppend @SortOb @(PortSorts @s (UN SUB a)) @(PortSorts @s (UN SUB b)) r
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

-- | The open hypergraph with the given nodes, boundaries and boxes. The first argument lists the
-- sorts of the nodes, and a node is referred to by its position in that list, counting from 0. The
-- second and third arguments give, for each wire of @as@ and of @bs@ in order, the node it is
-- attached to, and each box lists the nodes of its inputs and of its outputs. A node that occurs
-- several times joins all those wires and ports. Fails with a message unless every node referred
-- to exists and every wire has a sort isomorphic to that of its node.
--
-- The product of a box @a@ from @x@ to @y@ and a box @b@ from @y@ to @z@ has nodes of the sorts
-- @x@, @y@ and @z@, with @y@ shared between the boxes:
--
-- > openHypergraph @'[x] @'[z] [sx, sy, sz] [0] [2] [Box a [0] [1], Box b [1] [2]]
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

-- | 'openHypergraph' without its checks, with the same arguments: the boundaries must have as many
-- wires as their sorts, every wire and box must be attached to nodes that exist, and every wire must
-- have the sort of its node. Only for hypergraphs that satisfy this by construction, such as those
-- that 'simplify' is given, which trusts the sorts to be equal.
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

-- | An open hypergraph whose boundaries are known at runtime, for replacing a labelled box.
type SomeHypergraph :: Kind -> Type -> Type
data SomeHypergraph s l where
  SomeHypergraph :: (a :: OPENHG s l) ~> b -> SomeHypergraph s l

-- | Replace every box by the diagram assigned to its label. Each replacement must have as many
-- inputs and outputs as the box, in the same order, with isomorphic sorts. All replacements are
-- glued together in one union-find pass. Shared nodes, repeated ports and isolated nodes are kept.
-- Replacement labels are not substituted again.
--
-- Adapted from the functor-application construction in §9 of Wilson and Zanasi,
-- <https://arxiv.org/abs/2305.01041 Data-Parallel Algorithms for String Diagrams>, restricted to an
-- identity object map. This implementation uses maps and union-find rather than the paper's
-- data-parallel representation.
substitute
  :: forall {s} l m a b
   . (DecidableIso s)
  => (l -> SomeHypergraph s m)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s m))
substitute replace hg =
  hg // do
    (nodes, ins, outs, boxes) <- substituteParts byIso replace (hypergraphParts hg)
    P.pure (unsafeOpenHypergraph nodes ins outs boxes)

-- | Apply an object map and a generator map to an open hypergraph. Each source sort becomes a list
-- of target sorts, and each box is replaced by a diagram with the expanded inputs and outputs.
-- Every occurrence of a node uses the same expanded nodes, including repeated ports and boundaries.
-- An empty list removes a node; an isolated node expands to one isolated node per target sort.
-- The resulting boundaries are known at runtime, so the result is a 'SomeHypergraph'.
--
-- The object map must send isomorphic source sorts to lists of pairwise isomorphic target sorts
-- for composition to be preserved. Replacement boundaries are checked as in 'substitute'.
--
-- Adapted from the functor-application construction in §9 of Wilson and Zanasi,
-- <https://arxiv.org/abs/2305.01041 Data-Parallel Algorithms for String Diagrams>.
-- This implementation uses lists, maps and union-find rather than the paper's data-parallel representation.
substituteWith
  :: forall {s} {t} l m a b
   . (DecidableIso t)
  => (SomeSort s -> [SomeSort t])
  -> (l -> SomeHypergraph t m)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (SomeHypergraph t m)
substituteWith = substituteWithAligned byIso

-- | 'substituteWith' without comparing sorts. Replacement boundaries must have the sorts
-- specified by the object map, in order. Arity is still checked. For typed primitive translations
-- whose source and replacement ports agree by construction; otherwise use 'substituteWith'.
unsafeSubstituteWith
  :: forall {s} {t} l m a b
   . (SomeSort s -> [SomeSort t])
  -> (l -> SomeHypergraph t m)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (SomeHypergraph t m)
unsafeSubstituteWith = substituteWithAligned trusted

substituteWithAligned
  :: forall {s} {t} l m a b
   . Align t
  -> (SomeSort s -> [SomeSort t])
  -> (l -> SomeHypergraph t m)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (SomeHypergraph t m)
substituteWithAligned al mapSort replace hg = do
  let (original, ins, outs, boxes) = hypergraphParts hg
      expanded = P.fmap mapSort original
      sizes = P.fmap P.length expanded
      offsets = P.scanl (P.+) 0 sizes
      segments = M.fromList (P.zip [0 ..] (P.zipWith (\offset n -> [offset .. offset P.+ n P.- 1]) offsets sizes))
      ports = P.concatMap (segments M.!)
  (nodes, inputs', outputs', boxes') <-
    substituteParts
      al
      replace
      (P.concat expanded, ports ins, ports outs, [Box x (ports i) (ports o) | Box x i o <- boxes])
  let sortAt = M.fromList (P.zip [0 ..] nodes)
  reifySorts (P.fmap (sortAt M.!) inputs') \ @as ->
    reifySorts (P.fmap (sortAt M.!) outputs') \ @bs ->
      P.pure (SomeHypergraph (unsafeOpenHypergraph @m @as @bs nodes inputs' outputs' boxes'))

substituteParts
  :: forall {s} l m
   . Align s
  -> (l -> SomeHypergraph s m)
  -> ([SomeSort s], [P.Int], [P.Int], [Box l P.Int])
  -> P.Either P.String ([SomeSort s], [P.Int], [P.Int], [Box m P.Int])
substituteParts al replace (original, ins, outs, bs) = do
  let sortAt = M.fromList (P.zip [0 ..] original)
      add (offset, ns, boxes, joins) (Box x i o) =
        case replace x of
          SomeHypergraph replacement ->
            let (nodes, ri, ro, rb) = hypergraphParts replacement
                replacementSorts = M.fromList (P.zip [0 ..] nodes)
                matches ports boundary =
                  lineUpAll al (P.fmap (sortAt M.!) ports) (P.fmap (replacementSorts M.!) boundary)
                shift n = offset P.+ n
            in if matches i ri P.&& matches o ro
                 then
                   P.Right
                     ( offset P.+ P.length nodes
                     , nodes : ns
                     , P.fmap (P.fmap shift) rb : boxes
                     , (P.zip i (P.fmap shift ri) P.++ P.zip o (P.fmap shift ro)) : joins
                     )
                 else P.Left "substitute: a replacement boundary has different arity or sorts"
  (nodeCount, chunks, boxes, joins) <- foldM add (P.length original, [original], [], []) bs
  let nodeSorts = P.concat (P.reverse chunks)
      root = unionFind (P.concat joins)
      roots = M.fromList [(n, root n) | n <- [0 .. nodeCount P.- 1]]
      quotient = M.fromList (P.zip (M.elems roots) nodeSorts)
      indices = M.fromList (P.zip (M.keys quotient) [0 ..])
      renumber = (M.!) (P.fmap (indices M.!) roots)
  P.pure
    ( M.elems quotient
    , P.fmap renumber ins
    , P.fmap renumber outs
    , P.fmap (P.fmap renumber) (P.concat (P.reverse boxes))
    )

hypergraphParts :: forall {s} l a b. (a :: OPENHG s l) ~> b -> ([SomeSort s], [P.Int], [P.Int], [Box l P.Int])
hypergraphParts (DecCospan @c (Sub (FinHask l)) (Sub (FinHask r)) (Boxes bs)) =
  ( sortList @s @(PortSorts @s (UN SUB c))
  , P.fmap unPort (M.elems l)
  , P.fmap unPort (M.elems r)
  , P.fmap (P.fmap unPort) bs
  )
  where
    unPort (Port i) = i

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

-- | Wiring operations, feedback and box scheduling. 'permutations' and 'copyDiscard' reject
-- cycles; 'frobenius' supplies its cup-and-cap trace. 'tracedWith' replaces the feedback policy
-- with the target's trace while keeping the wiring operations and contraction plan.
-- Read-back reduces estimated swap cost; 'layered' also places independent boxes side by side.
type Wiring :: Kind -> Type
data Wiring s = Wiring
  { wiringFeedback :: Feedback s
  , wiringScheduling :: Scheduling
  , wiringSize :: P.Maybe (SomeSort s -> P.Int)
  , runWiring
      :: forall l a b
       . Align s
      -> Feedback s
      -> Scheduling
      -> (SomeSort s -> P.Int)
      -> (l -> SomeArrow s)
      -> (a :: OPENHG s l) ~> b
      -> P.Either P.String (WireSorts a ~> WireSorts b)
  }

-- | Only permutations: every node has one producer and one consumer. Nullary boxes and scalars
-- are allowed; copying, merging and discarding need stronger wiring operations. With 'tracedWith',
-- isolated loops are traced identities.
permutations :: (SymMonoidal s) => Wiring s
permutations = Wiring acyclic Sequential P.Nothing (\al fb mode sizeFn -> readBackDirected al fb mode sizeFn (P.== 1) permuteWires)
  where
    permuteWires bundle wanted =
      let positions = M.fromList (P.zip bundle [0 ..])
      in permuteThen (P.fmap (positions M.!) wanted)

-- | Each node has one producer and any number of consumers. Copy when a wire branches and
-- discard it when unused. Boxes with unused outputs still run; copying and discarding need not
-- be natural. Directed cycles are rejected unless 'tracedWith' enables the target's trace.
-- With tracing, nodes without producers feed themselves and their consumers through copying.
copyDiscard :: (CopyDiscard s) => Wiring s
copyDiscard =
  Wiring
    acyclic
    Sequential
    P.Nothing
    (\al fb mode sizeFn -> readBackDirected al fb mode sizeFn (P.const P.True) copyWires)

-- | Frobenius spiders with sizes from 'Sized', planned as in 'frobeniusWith'.
frobenius :: (Hypergraph s, Sized s) => Wiring s
frobenius = frobeniusWith sizeFromSized

-- | Frobenius spiders with the given wire sizes. State boxes are contracted as a tree, using
-- the cheaper of numpy's greedy order and min-fill elimination. Remaining boxes follow a path;
-- nodes are merged and discarded as soon as their other uses allow. This preserves the
-- contraction planner used by 'Proarrow.Tools.Einsum.einsum'. Feedback uses the trace from
-- Frobenius cups and caps. The given sizes also weight swap reduction, including wire routing
-- within state contractions; routing preserves the contraction tree and its eliminated indices.
frobeniusWith :: (Hypergraph s) => (SomeSort s -> P.Int) -> Wiring s
frobeniusWith sizeFn = Wiring hypergraphTrace Sequential (P.Just sizeFn) readBackFrobenius

-- | Use the target's trace for feedback, replacing the wiring's default feedback policy.
-- For example, @tracedWith copyDiscard@ supports copying, discarding and directed cycles.
tracedWith :: (TracedMonoidal s) => Wiring s -> Wiring s
tracedWith wiring = wiring{wiringFeedback = traced}

-- | Place independent boxes side by side with tensor, routing wires between layers. Swap reduction
-- uses the wiring's existing sizes, or 'Sized' when no sizes were supplied. Each crossing is weighted
-- by the product of the wire sizes. Wiring operations and feedback are unchanged.
-- Without this modifier boxes are placed one at a time, with uniform swap costs unless the wiring
-- supplies sizes, as 'frobenius' and 'frobeniusWith' do.
layered :: (Sized s) => Wiring s -> Wiring s
layered wiring =
  wiring{wiringScheduling = Layered, wiringSize = P.Just (fromMaybe sizeFromSized (wiringSize wiring))}

data Scheduling = Sequential | Layered

-- | How to close feedback wires, independently of the wiring operations.
type Feedback :: Kind -> Type
data Feedback s = Feedback
  { allowsCycles :: P.Bool
  , closeFeedback
      :: forall us xs ys
       . Sorts (us :: [s])
      -> Sorts xs
      -> Sorts ys
      -> (us ++ xs) ~> (us ++ ys)
      -> P.Either P.String (xs ~> ys)
  }

-- | Reject directed feedback. No trace constraint is required.
acyclic :: forall s. Feedback s
acyclic = Feedback P.False close
  where
    close
      :: forall us xs ys
       . Sorts (us :: [s])
      -> Sorts xs
      -> Sorts ys
      -> (us ++ xs) ~> (us ++ ys)
      -> P.Either P.String (xs ~> ys)
    close Nil _ _ f = P.Right f
    close _ _ _ _ = P.Left "readBack: feedback requires a trace"

-- | Close feedback with the target's trace. Requires no copying or merging.
traced :: forall s. (TracedMonoidal s) => Feedback s
traced = Feedback P.True (\us xs ys f -> P.Right (traceSorts (\ @u @x @y -> coact @Tensor @(Hom s) @u @x @y) us xs ys f))

-- | Close feedback with the trace derived from Frobenius cups and caps ('traceHG'). This keeps
-- the cup-and-cap form of hypergraph diagrams and needs no separate 'TracedMonoidal' instance.
hypergraphTrace :: (Hypergraph s) => Feedback s
hypergraphTrace = Feedback P.True (\us xs ys f -> P.Right (traceSorts (\ @u @x @y -> traceHG @u @x @y) us xs ys f))

-- | Interpret a graph using the given wiring, for example @readBack copyDiscard interpret graph@
-- or @readBack (tracedWith permutations) interpret graph@.
-- Sorts supplied from outside are compared by 'DecidableIso'; boxes are transported along the
-- resulting isomorphisms. Unsupported incidences or feedback return an error.
readBack
  :: forall {s} l a b
   . (DecidableIso s)
  => Wiring s
  -> (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
readBack wiring =
  runWiring
    wiring
    (byIso @s)
    (wiringFeedback wiring)
    (wiringScheduling wiring)
    (fromMaybe (P.const 1) (wiringSize wiring))

-- | The read-back, with the sorts lined up by the given alignment.
readBackFrobenius
  :: forall {s} l a b
   . (SymMonoidal s, Supplies Frobenius s)
  => Align s
  -> Feedback s
  -> Scheduling
  -> (SomeSort s -> P.Int)
  -> (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
readBackFrobenius al fbChoice mode sizeFn interp hg =
  hg // do
    arrows0 <-
      interpretBoxes
        al
        (sortAt M.!)
        interp
        "readBack: the arrow of a label does not have the sorts of its box"
        labelled
    let arrows =
          M.union
            arrows0
            (M.fromList [(j, pieceArrow al nodeSort arrows0 (routeTree (P.toInteger P.. sizeFn P.. nodeSort) t)) | (j, t) <- merged])
    withListOf (P.fmap (nodeSort P.. KN) (feedback lt)) \fb ->
      let insS = sorts @s @(WireSorts a)
          outsS = sorts @s @(WireSorts b)
          start = appendListOf fb insS
          initial = P.fmap KN (feedback lt P.++ shapeIns shape)
          wanted = P.fmap KL (feedback lt) P.++ P.fmap (outKey lt) (shapeOuts shape)
          plan bundle0 (t, layer) =
            let entries = [gateEntry (outKey lt) bx | bx <- layer]
                need = P.concatMap entryInputs entries
                made = P.concatMap entryOutputs entries
                carry = [k | k <- nubOrd (bundle0 P.++ need), live lt t k P.|| k `P.elem` made]
                whole = P.fmap identityEntry carry P.++ entries
            in (P.concatMap entryOutputs whole, whole)
          planned = P.snd (List.mapAccumL plan initial (P.zip [1 ..] layers))
          ordered = orderLayers (P.toInteger P.. sizeFn P.. nodeSort) initial wanted planned
          (bundle, body) = buildLayers al (transition al nodeSort []) arrows initial (Built start Same) ordered
          final =
            transition
              al
              nodeSort
              (isolated shape boxes0)
              bundle
              wanted
              body
      in case final of
           Built ys whole -> case alignSteps al ys (appendListOf fb outsS) of
             P.Just to -> closeFeedback fbChoice fb insS outsS (arrowOf ys to . arrowOf start whole)
             P.Nothing -> P.error "readBack: the boundaries were planned with other sorts"
  where
    (shape, sortAt, labelled) = prepareReadBack hg
    nodeSort k = sortAt M.! keyNode k
    boxes0 = [(i, bx{label = ()}) | (i, bx) <- labelled]
    size ns = P.product [P.fromIntegral (sizeFn (sortAt M.! n)) :: P.Double | n <- Set.toList ns]
    (boxesIx, merged) = pathBoxes boxes0 (contractStates size shape boxes0)
    order = schedule size shape boxesIx
    layers = boxLayers mode (feedback (lifetimes shape boxesIx (P.fmap (: []) order))) order
    lt = lifetimes shape boxesIx layers

-- Directed readers keep one wire per available node between boxes. Routing supplies the
-- current inputs and retains only those nodes needed by later boxes or the output boundary.
readBackDirected
  :: forall {s} l a b
   . (SymMonoidal s)
  => Align s
  -> Feedback s
  -> Scheduling
  -> (SomeSort s -> P.Int)
  -> (P.Int -> P.Bool)
  -> (forall xs. [Key] -> [Key] -> Built (xs :: [s]) -> Built xs)
  -> (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
readBackDirected al fbChoice mode sizeFn acceptsConsumers route interp hg =
  hg // do
    let (shape@(Shape _ ins outs), sortAt, numbered) = prepareReadBack hg
    (order, fbNodes) <- directedOrder (allowsCycles fbChoice) acceptsConsumers shape numbered
    arrows <- interpretBoxes al (sortAt M.!) interp "readBack: an arrow does not fit its box" numbered
    withListOf (P.fmap (sortAt M.!) fbNodes) \fb -> do
      let insS = sorts @s @(WireSorts a)
          outsS = sorts @s @(WireSorts b)
          start = appendListOf fb insS
          produced = Set.fromList (P.concatMap (outputs P.. P.snd) numbered)
          feedbackOutputs = Set.intersection (Set.fromList fbNodes) produced
          made n = if n `Set.member` feedbackOutputs then KL n else KN n
          wanted = P.fmap made fbNodes P.++ P.fmap KN outs
          layers = boxLayers mode fbNodes order
          uses = P.zip [0 :: P.Int ..] layers
          lastUse =
            M.fromListWith
              P.max
              ([(n, P.length layers) | n <- wanted] P.++ [(KN n, j) | (j, layer) <- uses, (_, bx) <- layer, n <- inputs bx])
          plan bundle0 (j, layer) =
            let carry = P.filter (\n -> M.findWithDefault (-1) n lastUse P.> j) bundle0
                entries = P.fmap identityEntry carry P.++ P.fmap (gateEntry made) layer
            in (P.concatMap entryOutputs entries, entries)
          initial = P.fmap KN (fbNodes P.++ ins)
          planned = P.snd (List.mapAccumL plan initial uses)
          ordered = orderLayers (P.toInteger P.. sizeFn P.. (sortAt M.!) P.. keyNode) initial wanted planned
          (bundle, body) = buildLayers al route arrows initial (Built start Same) ordered
      case route bundle wanted body of
        Built ys whole -> case alignSteps al ys (appendListOf fb outsS) of
          P.Just into -> closeFeedback fbChoice fb insS outsS (arrowOf ys into . arrowOf start whole)
          P.Nothing -> P.Left "readBack: the output boundary has other sorts"

-- Copy each available wire to its requested multiplicity, then permute the individual copies.
copyWires :: forall {s} xs. (CopyDiscard s) => [Key] -> [Key] -> Built (xs :: [s]) -> Built xs
copyWires bundle wanted body = permuteThen permutation (expand bundle `afterBuilt` body)
  where
    counts = M.fromListWith (P.+) [(n, 1 :: P.Int) | n <- wanted]
    count n = M.findWithDefault 0 n counts
    expanded = P.concatMap (\n -> P.replicate (count n) n) bundle
    numbered ns = P.snd (List.mapAccumL number M.empty ns)
    number seen n =
      let i = M.findWithDefault (0 :: P.Int) n seen
      in (M.insert n (i P.+ 1) seen, (n, i))
    positions = M.fromList (P.zip (numbered expanded) [0 ..])
    permutation = P.fmap (positions M.!) (numbered wanted)
    expand :: [Key] -> Sorts (ws :: [s]) -> Built ws
    expand [] Nil = Built Nil Same
    expand (n : ns) (Cons @x xs) = beside (single @x) (copies @x (count n)) xs (expand ns xs)
    expand _ _ = P.error "readBack: the bundle has other sorts"

-- The same node numbering is used by the planners and by box interpretation.
prepareReadBack
  :: forall {s} l a b
   . (a :: OPENHG s l) ~> b
  -> (Shape, M.Map P.Int (SomeSort s), [(P.Int, Box l P.Int)])
prepareReadBack hg =
  let (nodes, ins, outs, boxes) = hypergraphParts hg
  in (Shape [0 .. P.length nodes P.- 1] ins outs, M.fromList (P.zip [0 ..] nodes), P.zip [0 ..] boxes)

interpretBoxes
  :: forall {s} l
   . Align s
  -> (P.Int -> SomeSort s)
  -> (l -> SomeArrow s)
  -> P.String
  -> [(P.Int, Box l P.Int)]
  -> P.Either P.String (M.Map P.Int (SomeArrow s))
interpretBoxes al nodeSort interp message = P.fmap M.fromList P.. P.traverse checkBox
  where
    checkBox (i, Box x is os) = case interp x of
      arrow@(SomeArrow xs ys _)
        | lineUpAll al (someOfList xs) (P.fmap nodeSort is)
            P.&& lineUpAll al (someOfList ys) (P.fmap nodeSort os) ->
            P.Right (i, arrow)
        | P.otherwise -> P.Left message

-- Each node has at most one producer. With copying and tracing, a node without a producer
-- feeds itself and its consumers. Cut unavailable inputs of the first blocked box to schedule cycles.
directedOrder
  :: P.Bool
  -> (P.Int -> P.Bool)
  -> Shape
  -> [(P.Int, Box l P.Int)]
  -> P.Either P.String ([(P.Int, Box l P.Int)], [P.Int])
directedOrder canTrace acceptsConsumers sh boxes
  | P.not (P.all acceptsProducer (shapeNodes sh)) =
      P.Left "readBack: every node must have one producer"
  | P.not (P.all (\n -> n `Set.member` loops P.|| acceptsConsumers (M.findWithDefault 0 n consumerCounts)) (shapeNodes sh)) =
      P.Left "readBack: unsupported number of consumers"
  | P.not canTrace P.&& P.not (Set.null loops) = P.Left "readBack: isolated loops require a trace"
  | P.otherwise = go available0 ready counts [] (Set.toDescList sources)
  where
    producers = M.fromListWith (P.+) [(n, 1 :: P.Int) | n <- shapeIns sh P.++ P.concatMap (outputs P.. P.snd) boxes]
    consumerCounts = M.fromListWith (P.+) [(n, 1 :: P.Int) | n <- shapeOuts sh P.++ P.concatMap (inputs P.. P.snd) boxes]
    sources = Set.fromList (shapeNodes sh) `Set.difference` M.keysSet producers
    loops = sources `Set.difference` M.keysSet consumerCounts
    acceptsProducer n = case M.findWithDefault 0 n producers of
      1 -> P.True
      0 -> n `Set.member` loops P.|| (canTrace P.&& acceptsConsumers (1 P.+ M.findWithDefault 0 n consumerCounts))
      _ -> P.False
    available0 = Set.union sources (Set.fromList (shapeIns sh))
    counts = M.fromList [(i, P.length (P.filter (`Set.notMember` available0) (inputs bx))) | (i, bx) <- boxes]
    ready = M.keysSet (M.filter (P.== 0) counts)
    consumers = M.fromListWith (P.++) [(n, [i]) | (i, bx) <- boxes, n <- inputs bx]
    table = M.fromList boxes
    release acc n = P.foldl releaseBox acc (M.findWithDefault [] n consumers)
    releaseBox acc@(queue, remaining) i = case M.lookup i remaining of
      P.Nothing -> acc
      P.Just count ->
        let count' = count P.- 1
        in (if count' P.== 0 then Set.insert i queue else queue, M.insert i count' remaining)
    go available queue remaining acc cutsRev = case Set.minView queue of
      P.Nothing -> case M.lookupMin remaining of
        P.Nothing -> P.Right (P.reverse acc, P.reverse cutsRev)
        P.Just (i, _)
          | canTrace ->
              let missing = Set.fromList (inputs (table M.! i)) `Set.difference` available
                  ns = Set.toList missing
                  (next, counts') = P.foldl release (queue, remaining) ns
              in go (Set.union available missing) next counts' acc (P.reverse ns P.++ cutsRev)
          | P.otherwise -> P.Left "readBack: a directed cycle requires a trace"
      P.Just (i, rest) ->
        let bx = table M.! i
            fresh = Set.fromList (outputs bx) `Set.difference` available
            (next, counts') = P.foldl release (rest, M.delete i remaining) (Set.toList fresh)
        in go (Set.union available fresh) next counts' ((i, bx) : acc) cutsRev

-- ** Planning

-- Pack the existing order into earliest dependency layers. Feedback inputs are supplied by the
-- trace, independently of the outputs that close it.
boxLayers :: Scheduling -> [P.Int] -> [(P.Int, Box l P.Int)] -> [[(P.Int, Box l P.Int)]]
boxLayers Sequential _ order = P.fmap (: []) order
boxLayers Layered feedbackNodes order =
  P.fmap P.reverse (M.elems (M.fromListWith (P.++) [(t, [bx]) | (t, bx) <- placed]))
  where
    cut = Set.fromList feedbackNodes
    (_, placed) = List.mapAccumL place M.empty order
    place made bx@(_, b) =
      let t :: P.Int
          t = 1 P.+ P.maximum (0 : [M.findWithDefault 0 n made | n <- inputs b, n `Set.notMember` cut])
          made' = P.foldr (\n -> M.insertWith P.max n t) made (outputs b)
      in (made', (t, bx))

-- Carried wires participate in layout as identity boxes, without adding hypergraph nodes.
data LayerEntry = LayerEntry
  { entryInputs :: [Key]
  , entryOutputs :: [Key]
  , entryBox :: P.Maybe P.Int
  }

identityEntry :: Key -> LayerEntry
identityEntry k = LayerEntry [k] [k] P.Nothing

gateEntry :: (P.Int -> Key) -> (P.Int, Box l P.Int) -> LayerEntry
gateEntry made (i, bx) = LayerEntry (P.fmap KN (inputs bx)) (P.fmap made (outputs bx)) (P.Just i)

-- Four alternating sweeps exchange adjacent entries only when the total estimated routing cost
-- decreases. Layer membership and each box's port order stay fixed; ties retain their order.
orderLayers
  :: (Key -> P.Integer) -> [Key] -> [Key] -> [[LayerEntry]] -> [[LayerEntry]]
orderLayers size initial wanted layers0 =
  P.snd (List.foldl' sweep start passes)
  where
    -- Start identities near their incoming positions, even across several idle layers.
    -- Moving them one layer at a time can require cost-neutral swaps.
    seeded = P.snd (List.mapAccumL seed initial layers0)
    seed bundle layer =
      let positions = M.fromList (P.zip bundle [0 :: P.Int ..])
          position entry = P.minimum (P.length bundle : [i | k <- entryInputs entry, P.Just i <- [M.lookup k positions]])
          ordered = List.sortOn position layer
      in (P.concatMap entryOutputs ordered, ordered)
    originalCost = cost layers0
    seededCost = cost seeded
    start
      | originalCost P.== 0 P.|| originalCost P.<= seededCost = (originalCost, layers0)
      | P.otherwise = (seededCost, seeded)
    cost layers =
      P.sum
        ( P.zipWith
            crossings
            (initial : P.fmap (P.concatMap entryOutputs) layers)
            (P.fmap (P.concatMap entryInputs) layers P.++ [wanted])
        )
    -- Shared wires use the same position; Frobenius merging is an estimate of spider routing.
    crossings from to =
      let positions = M.fromList (P.zip from [0 :: P.Int ..])
          edges = [(i, size k) | k <- to, P.Just i <- [M.lookup k positions]]
      in weightedInversions edges
    passes :: [[(P.Int, P.Int)]]
    passes = [forward, backward, forward, backward]
    forward = [(i, j) | (i, layer) <- P.zip [0 ..] layers0, j <- [0 .. P.length layer P.- 2]]
    backward = P.reverse forward
    sweep current@(0, _) _ = current
    sweep current [] = current
    sweep current (move : rest) = sweep (improve current move) rest
    improve current@(best, layers) (i, j) = case P.splitAt i layers of
      (pre, layer : rest) ->
        let from = case P.reverse pre of
              [] -> initial
              previous : _ -> P.concatMap entryOutputs previous
            to = case rest of
              [] -> wanted
              following : _ -> P.concatMap entryInputs following
            -- Reordering a layer changes only its incoming and outgoing frontiers.
            localCost entries = crossings from (P.concatMap entryInputs entries) P.+ crossings (P.concatMap entryOutputs entries) to
            candidate = exchangeAt j layer
            next = best P.+ localCost candidate P.- localCost layer
        in if next P.< best then (next, pre P.++ (candidate : rest)) else current
      _ -> current
    exchangeAt n xs = case P.splitAt n xs of
      (pre, a : b : rest) -> pre P.++ (b : a : rest)
      _ -> xs

-- Crossing costs use Integer so large object sizes do not overflow during comparison.
weightedInversions :: [(P.Int, P.Integer)] -> P.Integer
weightedInversions edges = P.sum [a P.* b | (i, a) : rest <- List.tails edges, (j, b) <- rest, i P.> j]

-- Reorder the exposed wires of proper subtrees. Changing one boundary affects only its own
-- transition and its parent's, so each accepted swap reduces their combined routing cost.
-- The root boundary, contraction tree and the indices eliminated at each node stay fixed.
routeTree :: (Key -> P.Integer) -> Tree -> Tree
routeTree size t0 = List.foldl' (\t backwards -> visit backwards (P.const 0) P.False t) t0 passes
  where
    passes :: [P.Bool]
    passes = [P.False, P.True, P.False, P.True]
    visit backwards above movable t =
      let rebuilt = case t of
            Leaf{} -> t
            Merge l r ks
              | backwards ->
                  let r' = visit backwards (\out -> routingCost (treeKeys l P.++ out) ks) P.True r
                      l' = visit backwards (\out -> routingCost (out P.++ treeKeys r') ks) P.True l
                  in Merge l' r' ks
              | P.otherwise ->
                  let l' = visit backwards (\out -> routingCost (out P.++ treeKeys r) ks) P.True l
                      r' = visit backwards (\out -> routingCost (treeKeys l' P.++ out) ks) P.True r
                  in Merge l' r' ks
          cost tree = routingCost (treeMade tree) (treeKeys tree) P.+ above (treeKeys tree)
          positions = [0 .. P.length (treeKeys rebuilt) P.- 2]
          improve current@(best, tree) i =
            let ks = treeKeys tree
                candidate = case P.splitAt i ks of
                  (pre, a : b : rest) -> setKeys (pre P.++ (b : a : rest)) tree
                  _ -> tree
                next = cost candidate
            in if next P.< best then (next, candidate) else current
      in if movable
           then P.snd (List.foldl' improve (cost rebuilt, rebuilt) (if backwards then P.reverse positions else positions))
           else rebuilt
    setKeys ks (Leaf i made _) = Leaf i made ks
    setKeys ks (Merge l r _) = Merge l r ks
    routingCost from to =
      let kinds = groupOrder from to (nubOrd (from P.++ to))
          ranks = M.fromList (P.zip kinds [0 :: P.Int ..])
          grouped wires = weightedInversions [(ranks M.! k, size k) | k <- wires]
      in grouped from P.+ grouped to

-- Route each frontier and tensor its gates with the identities of the carried wires.
buildLayers
  :: forall s (xs :: [s])
   . (SymMonoidal s)
  => Align s
  -> (forall ws. [Key] -> [Key] -> Built (ws :: [s]) -> Built ws)
  -> M.Map P.Int (SomeArrow s)
  -> [Key]
  -> Built xs
  -> [[LayerEntry]]
  -> ([Key], Built xs)
buildLayers al route arrows = go
  where
    go :: [Key] -> Built xs -> [[LayerEntry]] -> ([Key], Built xs)
    go bundle body [] = (bundle, body)
    go bundle body (layer : rest) =
      let need = P.concatMap entryInputs layer
          made = P.concatMap entryOutputs layer
          run :: forall ws. Sorts (ws :: [s]) -> Built ws
          run = build layer
      in go made (run `afterBuilt` route bundle need body) rest
    build :: forall ws. [LayerEntry] -> Sorts (ws :: [s]) -> Built ws
    build [] ws = Built ws Same
    build (entry : rest) ws = case entryBox entry of
      P.Nothing ->
        let (identities, remaining) = P.span (isNothing P.. entryBox) rest
        in carryThen (1 P.+ P.length identities) (build remaining) ws
      P.Just i -> case arrows M.! i of
        arrow@(SomeArrow ins _ _) -> case rest of
          [] -> boxThen al arrow ws
          _ -> splitSorts (lengthListOf ins) ws \pre post -> beside pre (boxThen al arrow pre) post (build rest post)

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

-- | Some of the boxes without inputs, contracted as a tree, with how many of them touch each node.
data Piece = Piece {pieceTree :: Tree, pieceCounts :: M.Map P.Int P.Int}

-- | The boxes without inputs contracted with each other as a tree, until no two share a node, in
-- the order of 'planContraction'.
contractStates :: (Set.Set P.Int -> P.Double) -> Shape -> [Ix] -> [Piece]
contractStates size sh bxs = P.fmap run (planContraction size (P.const P.True) needed (P.fmap touches states))
  where
    states = [b | b@(_, bx) <- bxs, P.null (inputs bx)]
    -- the nodes of the boundary and of the boxes with inputs
    needed =
      Set.fromList
        (shapeIns sh P.++ shapeOuts sh P.++ [n | b@(_, bx) <- bxs, P.not (P.null (inputs bx)), n <- Set.toList (touches b)])
    run (Factor k) = leaf (M.fromList (P.zip [0 ..] states) M.! k)
    run (Contract a b) = merge (run a) (run b)
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
      in Piece (Leaf i (P.fmap KN (outputs bx)) (keysIn open (P.fmap KN (outputs bx)))) counts
    merge a b =
      let counts = M.unionWith (P.+) (pieceCounts a) (pieceCounts b)
          open = openIn counts
      in Piece (Merge (pieceTree a) (pieceTree b) (keysIn open (treeKeys (pieceTree a) P.++ treeKeys (pieceTree b)))) counts

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

lifetimes :: Shape -> [Ix] -> [[Ix]] -> Lifetimes
lifetimes sh bxs layers = Lifetimes{feedback = fb, outKey = key, live = alive}
  where
    layerOf = M.fromList [(i, t) | (t, layer) <- P.zip [1 :: P.Int ..] layers, (i, _) <- layer]
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
  :: forall s
   . (SymMonoidal s, Supplies Frobenius s)
  => Align s -> (Key -> SomeSort s) -> M.Map P.Int (SomeArrow s) -> Tree -> SomeArrow s
pieceArrow al nodeSort arrows0 t0 = case go t0 of
  Built ys f -> SomeArrow Nil ys (arrowOf Nil f)
  where
    go :: Tree -> Built ('[] :: [s])
    go t = transition al nodeSort [] (treeMade t) (treeKeys t) (body t)
    body (Leaf i _ _) = boxThen al (arrows0 M.! i) Nil
    body (Merge l r _) = beside Nil (go l) Nil (go r)

-- | What is built so far followed by one spider per wire kind, also for the given kinds without
-- wires, between permutations that group the wires. Each step is composed onto what is built so far
-- by itself, so that in a category of matrices a state is only ever multiplied by one step.
transition
  :: forall s (xs :: [s])
   . (SymMonoidal s, Supplies Frobenius s)
  => Align s -> (Key -> SomeSort s) -> [Key] -> [Key] -> [Key] -> Built xs -> Built xs
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

-- | Read a primitive graph using the given wiring. Primitive sorts are trusted, so
-- 'DecidableIso' is unnecessary: for example, @simplify copyDiscard graph@ can execute a graph
-- as a Haskell function.
simplify
  :: forall {k} a b
   . Wiring k
  -> (a :: SIMPLIFY k) ~> b
  -> P.Either P.String (WireSorts a ~> WireSorts b)
simplify wiring =
  runWiring
    wiring
    trusted
    (wiringFeedback wiring)
    (wiringScheduling wiring)
    (fromMaybe (P.const 1) (wiringSize wiring))
    (\(Prim arrow) -> arrow)

-- | Interpret a primitive graph in its hypergraph target, with wire sizes from 'Sized'.
-- This is 'simplify' with 'frobenius': every graph is supported and
-- primitive sorts are trusted, so the result needs no 'P.Either'.
simplifyHypergraph
  :: forall {k} a b
   . (Hypergraph k, Sized k)
  => (a :: SIMPLIFY k) ~> b
  -> WireSorts a ~> WireSorts b
simplifyHypergraph = P.either P.error P.id P.. simplify frobenius

-- | 'simplifyHypergraph' with every box bent into a state on all its wires, its inputs turned into outputs
-- with cups. The read-back then contracts the whole network in the order of 'planContraction',
-- instead of following the flow from inputs to outputs, and needs no traces for cycles. For
-- computing with a term rather than drawing it, as the result is drawn with cups and caps.
simplifyFlat :: forall {k} a b. (Hypergraph k, Sized k) => (a :: SIMPLIFY k) ~> b -> WireSorts a ~> WireSorts b
simplifyFlat (DecCospan l r (Boxes bxs)) =
  simplifyHypergraph (DecCospan l r (Boxes (P.fmap bent bxs)))
  where
    bent bx@(Box (Prim (SomeArrow xs ys f)) is os)
      | P.null is = bx
      | P.otherwise = Box (Prim (bendInputs xs ys f)) [] (P.reverse is P.++ os)

-- | An arrow with its inputs bent over to its outputs with cups, one at a time from the first, so
-- that the state's wires are the inputs in reverse order followed by the outputs.
bendInputs :: forall {s} (as :: [s]) bs. (Hypergraph s) => Sorts as -> Sorts bs -> as ~> bs -> SomeArrow s
bendInputs Nil ys f = SomeArrow Nil ys f
bendInputs (Cons @x @rest xs) ys f =
  withIsListOf xs P.$ bendInputs xs (Cons @x ys) ((obj @'[x] ** f) . (cupS @x ** obj @rest))

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

-- | Leave the first wires unchanged while building a step on the rest.
carryThen
  :: forall {s} (xs :: [s])
   . (Monoidal s)
  => P.Int
  -> (forall (ys :: [s]). Sorts ys -> Built ys)
  -> Sorts xs
  -> Built xs
carryThen n build xs = splitSorts n xs \pre post -> beside pre (Built pre Same) post (build post)

-- | The box on the first wires, and the rest of the wires unchanged.
boxThen :: (Monoidal s) => Align s -> SomeArrow s -> Sorts (xs :: [s]) -> Built xs
boxThen al (SomeArrow as bs f) xs = splitSorts (lengthListOf as) xs \pre post -> case alignSteps al pre as of
  P.Just into -> beside pre (Built bs (Arrow (f . arrowOf pre into))) post (Built post Same)
  P.Nothing -> P.error "readBack: a box was planned on wires of other sorts"

-- | What is built so far followed by its wires in the order that @p@ lists them, as adjacent swaps
-- composed one at a time: the wire at position @j@ of the result is wire @p !! j@ before.
permuteThen :: (SymMonoidal s) => [P.Int] -> Built (xs :: [s]) -> Built xs
permuteThen p built0 = P.foldl (\built i -> swapThen i `afterBuilt` built) built0 (P.reverse (bubble p []))
  where
    -- the positions of the adjacent swaps that sort @p@
    bubble ps acc = case [i | (i, (a, b)) <- P.zip [0 ..] (P.zip ps (P.drop 1 ps)), a P.> b] of
      [] -> P.reverse acc
      i : _ -> bubble (P.take i ps P.++ [ps P.!! (i P.+ 1), ps P.!! i] P.++ P.drop (i P.+ 2) ps) (i : acc)

-- | The swap of the wires at positions @i@ and @i + 1@.
swapThen :: (SymMonoidal s) => P.Int -> Sorts (xs :: [s]) -> Built xs
swapThen 0 (Cons @x (Cons @y rest)) = Built (Cons @y (Cons @x rest)) (Arrow (swap2 @x @y ** withIsListOf rest id))
swapThen i (Cons @x rest) = case swapThen (i P.- 1) rest of
  Built ys f -> Built (Cons @x ys) (Arrow (obj1 @x ** arrowOf rest f))
swapThen _ Nil = P.error "readBack: a swap beyond the wires was planned"

-- | For each sort, a spider from the given number of wires to the given number.
spidersThen
  :: (SymMonoidal s, Supplies Frobenius s) => Align s -> [(SomeSort s, P.Int, P.Int)] -> Sorts (xs :: [s]) -> Built xs
spidersThen _ [] Nil = Built Nil Same
spidersThen _ [] _ = P.error "readBack: wires without a spider were planned"
spidersThen al ((x, c, m) : rest) xs = splitSorts c xs \pre post -> beside pre (spider al x c m pre) post (spidersThen al rest post)

-- | The spider of a sort from @c@ wires to @m@: merging all of them, then copying the result.
spider
  :: (SymMonoidal s, Supplies Frobenius s) => Align s -> SomeSort s -> P.Int -> P.Int -> Sorts (pre :: [s]) -> Built pre
spider al (Some @x) c m pre
  | c P.== 1 P.&& m P.== 1 = Built pre Same
  | P.otherwise = case copies @x m of Built ys f -> Built ys (Arrow (arrowOf (single @x) f . merges @x al pre))

-- | All the wires merged into one of sort @x@, each lined up with it first, or the unit of @x@ when
-- there are none.
merges :: forall {s} (x :: s) pre. (SymMonoidal s, Supplies Frobenius s, Ob x) => Align s -> Sorts pre -> pre ~> '[x]
merges _ Nil = memptyS @x
merges al (Cons @y Nil) = toX @y al
merges al (Cons @y rest@Cons{}) = mappendS @x . (toX @y al ** merges @x al rest)

toX :: forall {s} y (x :: s). (Monoidal s, Ob x, Ob y) => Align s -> '[y] ~> '[x]
toX al = case al @y @x of
  P.Just a -> arrowOf (single @y) a
  P.Nothing -> P.error "readBack: a spider was planned on wires of other sorts"

-- | One wire of sort @x@ copied to @m@, or discarded when @m@ is 0.
copies :: forall {s} (x :: s). (CocommutativeComonoid x) => P.Int -> Built '[x]
copies 0 = Built Nil (Arrow (counitS @x))
copies 1 = Built (single @x) Same
copies 2 = Built (Cons @x (single @x)) (Arrow (comultS @x))
copies m = case copies @x (m P.- 1) of
  Built ys f -> Built (Cons @x ys) (Arrow ((obj1 @x ** arrowOf (single @x) f) . comultS @x))

-- | The trace over the first wires, @us@, which feeds their outputs back to their inputs.
traceSorts
  :: forall {s} (us :: [s]) xs ys
   . (SymMonoidal s)
  => (forall (u :: s) x y. (Ob u, Ob x, Ob y) => u ** x ~> u ** y -> x ~> y)
  -> Sorts us
  -> Sorts xs
  -> Sorts ys
  -> (us ++ xs) ~> (us ++ ys)
  -> xs ~> ys
traceSorts _ Nil _ _ f = f
traceSorts close us xs ys f =
  withIsListOf us P.$
    withIsListOf xs P.$
      withIsListOf ys P.$
        case (splitMany @us, splitMany @xs, concatMany @ys) of
          (splitUs@Objs, splitXs@Objs, concatYs@Objs) ->
            splitMany @ys
              . Str
                ( close @(Fold us) @(Fold xs) @(Fold ys)
                    (unStr ((concatMany @us ** concatYs) . f . (splitUs ** splitXs)))
                )
              . concatMany @xs
