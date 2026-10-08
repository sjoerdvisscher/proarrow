{-# LANGUAGE AllowAmbiguousTypes #-}

-- | __Open hypergraphs__ with typed wires: decorated cospans ("Proarrow.Category.Instance.DecoratedCospan")
-- of finite sets whose elements have sorts, decorated with labelled boxes. A morphism has nodes, each
-- of some sort, boxes attached to them, and two boundaries of sorted ports. It is a morphism of the
-- free hypergraph category on its boxes, and two such morphisms are equal by the Frobenius laws
-- exactly when they are 'isomorphic'.
--
-- The sorts are types of a kind @s@, known at runtime through 'Typeable', so that a computed
-- apex knows the sorts of its nodes. A list of sorts @xs@ gives the boundary @'Wires' xs@.
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
  , isomorphic

    -- * Read-back
  , SomeArrow (..)
  , someArrow
  , readBack

    -- * Simplifying
  , SIMPLIFY
  , prim
  , simplify
  ) where

import Control.Monad (foldM, msum)
import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Constraint, Type)
import Data.List qualified as List
import Data.Map.Strict qualified as M
import Data.Maybe (isJust)
import Data.Set qualified as Set
import Data.Type.Equality ((:~:) (..), (:~~:) (..), type (~))
import Data.Universe.Class (Finite (..), Universe (..))
import Type.Reflection (Typeable, eqTypeRep, typeRep)
import Prelude qualified as P

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.FinHask (FINHASK (..), FinHask (..))
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Applicative (Alternative (..))
import Proarrow.Category.Monoidal.Hypergraph (Hypergraph, traceHG)
import Proarrow.Category.Monoidal.Strictified
  ( Fold
  , Strictified (..)
  , concatMany
  , obj1
  , splitMany
  , swap2
  , withIsListOf
  , withObFold
  , type (++)
  )
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Colimit.Pushout (HasPushouts (..))
import Proarrow.Core (CategoryOf (..), OB, Ob', Promonad (..), UN, (//), type (:&&:))
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

-- * Sorts

-- | A sort of kind @s@, an object of the category of @s@, known at runtime. Sorts compare by their
-- type representation.
type SomeSort :: Type -> Type
type SomeSort s = SomeOf (SortOb @s)

-- | The evidence a sort carries: a runtime representation and objecthood.
type SortOb :: forall s. s -> Constraint
type SortOb @s = Typeable :&&: (Ob' :: s -> Constraint)

-- | The sorts of the ports of a sorted finite set.
type PortSorts :: forall s. FINHASK -> [s]
type family PortSorts a where
  PortSorts (FH (Port xs)) = xs

-- | The finite sets of ports with sorts of kind @s@, @'FH' ('Port' xs)@.
type Sorted :: Type -> OB FINHASK
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
type SORTED :: Type -> Type
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
type OPENHG :: Type -> Type -> Type
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
-- wire has the sort of its node and every node exists.
openHypergraph
  :: forall {s} l (as :: [s]) (bs :: [s])
   . (SortList as, SortList bs)
  => [SomeSort s]
  -> [P.Int]
  -> [P.Int]
  -> [Box l P.Int]
  -> P.Either P.String (Wires as ~> (Wires bs :: OPENHG s l))
openHypergraph nodeSorts ins outs boxList
  | P.length ins P./= lengthListOf (sorts @s @as) P.|| P.length outs P./= lengthListOf (sorts @s @bs) =
      P.Left "openHypergraph: a boundary has a different number of wires than its sorts"
  | P.any
      (\n -> n P.< 0 P.|| n P.>= P.length nodeSorts)
      (ins P.++ outs P.++ P.concat [inputs bx P.++ outputs bx | bx <- boxList]) =
      P.Left "openHypergraph: a wire or box is attached to a node that does not exist"
  | P.fmap (nodeSorts P.!!) ins P./= sortList @s @as P.|| P.fmap (nodeSorts P.!!) outs P./= sortList @s @bs =
      P.Left "openHypergraph: a wire does not have the sort of its node"
  | P.otherwise = reifySorts nodeSorts \ @ns ->
      P.Right
        ( DecCospan
            (Sub (FinHask (M.fromList (P.zip universeF (P.fmap (Port @_ @ns) ins)))))
            (Sub (FinHask (M.fromList (P.zip universeF (P.fmap (Port @_ @ns) outs)))))
            (Boxes (P.fmap (P.fmap Port) boxList))
        )

-- | Whether two open hypergraphs differ only in the names of their nodes and the order of their
-- boxes: a bijection between the nodes that keeps their sorts, agrees with both boundaries and takes
-- the boxes of one to those of the other.
isomorphic :: forall {s} l a b. (P.Eq l) => (a :: OPENHG s l) ~> b -> a ~> b -> P.Bool
isomorphic
  (DecCospan @c1 (Sub (FinHask l1)) (Sub (FinHask r1)) (Boxes bs1))
  (DecCospan @c2 (Sub (FinHask l2)) (Sub (FinHask r2)) (Boxes bs2)) =
    -- the nodes that nothing is attached to can be matched up exactly when this holds
    List.sort (P.fmap sort1 nodes1) P.== List.sort (P.fmap sort2 nodes2)
      P.&& sameShapes (P.fmap shape bs1) (P.fmap shape bs2)
      P.&& isJust
        (extendAll (M.empty, M.empty) (P.zip (M.elems l1) (M.elems l2) P.++ P.zip (M.elems r1) (M.elems r2)) P.>>= boxes bs1 bs2)
    where
      nodes1 = universeF @(UN FH (UN SUB c1))
      nodes2 = universeF @(UN FH (UN SUB c2))
      sort1 = sortOf @s @(UN SUB c1)
      sort2 = sortOf @s @(UN SUB c2)
      shape (Box x i o) = (x, P.length i, P.length o)
      -- the boxes have the same labels and arities, counted with multiplicity
      sameShapes [] ys = P.null ys
      sameShapes (x : xs) ys = case List.break (P.== x) ys of
        (_, []) -> P.False
        (before, _ : after) -> sameShapes xs (before P.++ after)
      boxes [] _ m = P.Just m
      boxes (x : xs) ys m = msum [match x y m P.>>= boxes xs rest | (y, rest) <- picks ys]
      match (Box lx ix ox) (Box ly iy oy) m
        | lx P.== ly P.&& P.length ix P.== P.length iy P.&& P.length ox P.== P.length oy =
            extendAll m (P.zip ix iy P.++ P.zip ox oy)
        | P.otherwise = P.Nothing
      extendAll = foldM (P.flip extend)
      extend (x, y) (fwd, bwd)
        | sort1 x P./= sort2 y = P.Nothing
        | P.otherwise = case (M.lookup x fwd, M.lookup y bwd) of
            (P.Nothing, P.Nothing) -> P.Just (M.insert x y fwd, M.insert y x bwd)
            (P.Just y', P.Just x') | y' P.== y P.&& x' P.== x -> P.Just (fwd, bwd)
            _ -> P.Nothing
      picks :: [x] -> [(x, [x])]
      picks xs = [(x, before P.++ after) | (before, x : after) <- P.zip (List.inits xs) (List.tails xs)]

-- * Read-back

-- | An arrow of the strictified category of @s@ whose lists of sorts are known at runtime, such as
-- the interpretation of a box.
type SomeArrow :: Type -> Type
data SomeArrow s where
  SomeArrow :: forall {s} (as :: [s]) bs. Sorts as -> Sorts bs -> Strictified as bs -> SomeArrow s

-- | An arrow as one whose sorts are known at runtime.
someArrow :: forall {s} (as :: [s]) bs. (SortList as, SortList bs) => Strictified as bs -> SomeArrow s
someArrow = SomeArrow (sorts @s @as) (sorts @s @bs)

-- | The term of a hypergraph category that an open hypergraph stands for, given an arrow for each
-- label: its boxes in layers along the flow of their wires, with between two layers one spider per
-- node. A node that a box uses no later than a box makes it is fed back with a trace, which only a
-- cyclic hypergraph needs. Fails with a message when an arrow does not fit its box.
readBack
  :: forall {s} l a b
   . (Hypergraph s)
  => (l -> SomeArrow s)
  -> (a :: OPENHG s l) ~> b
  -> P.Either P.String (Strictified (WireSorts a) (WireSorts b))
readBack interp hg@(DecCospan @c (Sub (FinHask legIn)) (Sub (FinHask legOut)) (Boxes boxList)) =
  hg // do
    arrows <- M.fromList P.<$> P.traverse interpBox boxesIx
    P.pure P.$ withListOf (P.fmap (nodeSort P.. KN) feedback) \fb ->
      let insS = sorts @s @(WireSorts a)
          outsS = sorts @s @(WireSorts b)
          start = appendListOf fb insS
          (bundle, body) = P.foldl (step arrows) (P.fmap KN (feedback P.++ ins), Built start Same) (P.zip [1 ..] layers)
          final = transition isolated bundle (P.fmap KL feedback P.++ P.fmap outKey outs) `afterBuilt` body
      in case final of
           Built ys whole -> case eqSorts ys (appendListOf fb outsS) of
             P.Just Refl -> traceSorts fb insS outsS (arrowOf start whole)
             P.Nothing -> P.error "readBack: the boundaries were planned with other sorts"
  where
    nodes = universeF @(UN FH (UN SUB c))
    index = M.fromList (P.zip nodes [0 :: P.Int ..])
    sortC = sortOf @s @(UN SUB c)
    sortAt = M.fromList [(index M.! n, sortC n) | n <- nodes]
    nodeSort k = sortAt M.! keyNode k
    ins = P.fmap (index M.!) (M.elems legIn)
    outs = P.fmap (index M.!) (M.elems legOut)
    boxesIx = P.zip [0 :: P.Int ..] [P.fmap (index M.!) bx | bx <- boxList]
    -- a box depends on another when it uses a node the other makes
    dependsOn (i, bi) (j, bj) = i P./= j P.&& P.any (`P.elem` outputs bj) (inputs bi)
    layers = layer boxesIx
    layer [] = []
    layer remaining = case [bx | bx <- remaining, P.not (P.any (dependsOn bx) remaining)] of
      [] -> P.take 1 remaining : layer (P.drop 1 remaining)
      ready -> ready : layer [bx | bx <- remaining, P.fst bx `P.notElem` P.fmap P.fst ready]
    end = P.length layers P.+ 1
    layerOf = M.fromList [(i, t) | (t, ly) <- P.zip [1 :: P.Int ..] layers, (i, _) <- ly]
    madeAt = M.fromListWith (P.++) [(n, [layerOf M.! i]) | (i, bx) <- boxesIx, n <- outputs bx]
    usedAt = M.fromListWith (P.++) [(n, [layerOf M.! i]) | (i, bx) <- boxesIx, n <- inputs bx]
    layersOf n m = M.findWithDefault [] n m
    feedback = [n | n <- M.elems index, P.or [mk P.>= u | u <- layersOf n usedAt, mk <- layersOf n madeAt]]
    isFeedback n = n `P.elem` feedback
    attached = Set.fromList (ins P.++ outs P.++ P.concat [inputs bx P.++ outputs bx | (_, bx) <- boxesIx])
    -- a node attached to nothing is a closed loop, a spider without legs
    isolated = [KN n | n <- M.elems index, n `Set.notMember` attached]
    outKey n = if isFeedback n then KL n else KN n
    -- the layers after which a wire is still needed
    neededAt (KN n) = layersOf n usedAt P.++ [end | n `P.elem` outs, P.not (isFeedback n)]
    neededAt (KL _) = [end]
    step
      :: forall (xs :: [s])
       . M.Map P.Int (SomeArrow s)
      -> ([Key], Built xs)
      -> (P.Int, [(P.Int, Box l P.Int)])
      -> ([Key], Built xs)
    step arrows (bundle, body) (t, ly) =
      let need = P.concat [P.fmap KN (inputs bx) | (_, bx) <- ly]
          carry = [k | k <- nubOrd (bundle P.++ need), P.any (P.> t) (neededAt k)]
          run :: forall (ws :: [s]). Sorts ws -> Built ws
          run = boxesThen [arrows M.! i | (i, _) <- ly]
      in ( P.concat [P.fmap outKey (outputs bx) | (_, bx) <- ly] P.++ carry
         , run `afterBuilt` (transition [] bundle (need P.++ carry) `afterBuilt` body)
         )
    interpBox (i, Box x is os) = case interp x of
      arr@(SomeArrow xs ys _)
        | someOfList xs P.== P.fmap (nodeSort P.. KN) is P.&& someOfList ys P.== P.fmap (nodeSort P.. KN) os ->
            P.Right (i, arr)
        | P.otherwise -> P.Left "readBack: the arrow of a label does not have the sorts of its box"
    -- one spider per wire kind, also for the given kinds without wires, between permutations that
    -- group the wires; the permutation goes on the side with fewer wires where it can
    transition :: [Key] -> [Key] -> [Key] -> (forall (xs :: [s]). Sorts xs -> Built xs)
    transition extra from to xs =
      let order = if P.length from P.>= P.length to then nubOrd (from P.++ to) else nubOrd (to P.++ from)
          kinds = order P.++ [k | k <- extra, k `P.notElem` order]
          count k ks = P.length (P.filter (P.== k) ks)
          positions ks = [i | k <- kinds, i <- [j | (j, k') <- P.zip [0 ..] ks, k' P.== k]]
          identity = P.all (\k -> count k from P.== 1 P.&& count k to P.== 1) kinds
          spiders :: forall (ws :: [s]). Sorts ws -> Built ws
          spiders ws
            | identity = Built ws Same
            | P.otherwise = spidersThen [(nodeSort k, count k from, count k to) | k <- kinds] ws
      in (permuteThen (inverse (positions to)) `afterBuilt` (spiders `afterBuilt` permuteThen (positions from) xs))
    inverse p = P.fmap P.snd (List.sort (P.zip p [0 ..]))

-- * Simplifying

-- | Open hypergraphs whose boxes are arrows of @k@: the category to run a term of a hypergraph
-- category in, with the arrows it uses made boxes by 'prim', to 'simplify' it.
type SIMPLIFY :: Type -> Type
type SIMPLIFY k = OPENHG k (SomeArrow k)

-- | An arrow of @k@ between lists of objects as one box.
prim
  :: forall {k} (as :: [k]) bs. (SortList as, SortList bs) => Strictified as bs -> Wires as ~> (Wires bs :: SIMPLIFY k)
prim f = box (someArrow f)

-- | The term of @k@ that a term run in 'SIMPLIFY' stands for: its 'readBack', with each box the
-- arrow it was made from.
simplify :: forall {k} a b. (Hypergraph k) => (a :: SIMPLIFY k) ~> b -> Strictified (WireSorts a) (WireSorts b)
simplify t = case readBack P.id t of
  P.Right r -> r
  P.Left e -> P.error e

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
  Arrow :: Strictified xs ys -> Step xs ys

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

arrowOf :: (Monoidal s) => Sorts (xs :: [s]) -> Step xs ys -> Strictified xs ys
arrowOf xs Same = idSorts xs
arrowOf _ (Arrow f) = f

-- | Two built pieces side by side.
beside :: (Monoidal s) => Sorts (xs :: [s]) -> Built xs -> Sorts xs' -> Built xs' -> Built (xs ++ xs')
beside _ (Built ys Same) _ (Built ys' Same) = Built (appendListOf ys ys') Same
beside xs (Built ys f) xs' (Built ys' g) = Built (appendListOf ys ys') (Arrow (arrowOf xs f ** arrowOf xs' g))

-- | The identity, one wire at a time, so that tensoring onto it costs nothing in 'Strictified'.
idSorts :: (Monoidal s) => Sorts (xs :: [s]) -> Strictified xs xs
idSorts Nil = id
idSorts (Cons @x rest) = obj1 @x ** idSorts rest

-- | The list split after its first @n@ sorts.
splitSorts :: P.Int -> Sorts xs -> (forall pre post. (xs ~ (pre ++ post)) => Sorts pre -> Sorts post -> r) -> r
splitSorts 0 xs k = k Nil xs
splitSorts n (Cons @x rest) k = splitSorts (n P.- 1) rest \pre post -> k (Cons @x pre) post
splitSorts _ Nil _ = P.error "readBack: a split beyond the wires was planned"

eqSorts :: Sorts xs -> Sorts ys -> P.Maybe (xs :~: ys)
eqSorts Nil Nil = P.Just Refl
eqSorts (Cons @x xs) (Cons @y ys) = do
  HRefl <- eqTypeRep (typeRep @x) (typeRep @y)
  Refl <- eqSorts xs ys
  P.pure Refl
eqSorts _ _ = P.Nothing

single :: forall {s} (x :: s). (Typeable x, Ob' x) => Sorts '[x]
single = Cons @x Nil

-- | The boxes on the first wires, side by side, and the rest of the wires unchanged.
boxesThen :: (Monoidal s) => [SomeArrow s] -> Sorts (xs :: [s]) -> Built xs
boxesThen [] xs = Built xs Same
boxesThen (SomeArrow as bs f : rest) xs = splitSorts (lengthListOf as) xs \pre post -> case eqSorts pre as of
  P.Just Refl -> beside pre (Built bs (Arrow f)) post (boxesThen rest post)
  P.Nothing -> P.error "readBack: a box was planned on wires of other sorts"

-- | The wires in the order that @p@ lists them, as adjacent swaps: the wire at position @j@ of the
-- result is wire @p !! j@ of the source.
permuteThen :: (Hypergraph s) => [P.Int] -> Sorts (xs :: [s]) -> Built xs
permuteThen p xs0 = P.foldl (\built i -> swapThen i `afterBuilt` built) (Built xs0 Same) (P.reverse (bubble p []))
  where
    -- the positions of the adjacent swaps that sort @p@
    bubble ps acc = case [i | (i, (a, b)) <- P.zip [0 ..] (P.zip ps (P.drop 1 ps)), a P.> b] of
      [] -> P.reverse acc
      i : _ -> bubble (P.take i ps P.++ [ps P.!! (i P.+ 1), ps P.!! i] P.++ P.drop (i P.+ 2) ps) (i : acc)

-- | The swap of the wires at positions @i@ and @i + 1@.
swapThen :: (Hypergraph s) => P.Int -> Sorts (xs :: [s]) -> Built xs
swapThen 0 (Cons @x (Cons @y rest)) = Built (Cons @y (Cons @x rest)) (Arrow (swap2 @x @y ** idSorts rest))
swapThen i (Cons @x rest) = case swapThen (i P.- 1) rest of
  Built ys f -> Built (Cons @x ys) (Arrow (obj1 @x ** arrowOf rest f))
swapThen _ Nil = P.error "readBack: a swap beyond the wires was planned"

-- | For each sort, a spider from the given number of wires to the given number.
spidersThen :: (Hypergraph s) => [(SomeSort s, P.Int, P.Int)] -> Sorts (xs :: [s]) -> Built xs
spidersThen [] Nil = Built Nil Same
spidersThen [] _ = P.error "readBack: wires without a spider were planned"
spidersThen ((x, c, m) : rest) xs = splitSorts c xs \pre post -> beside pre (spider x c m pre) post (spidersThen rest post)

-- | The spider of a sort from @c@ wires to @m@: merging all of them, then copying the result.
spider :: (Hypergraph s) => SomeSort s -> P.Int -> P.Int -> Sorts (pre :: [s]) -> Built pre
spider (Some @x) c m pre
  | c P.== 1 P.&& m P.== 1 = Built pre Same
  | P.otherwise = case copies @x m of Built ys f -> Built ys (Arrow (arrowOf (single @x) f . merges @x pre))

-- | All the wires merged into one of sort @x@, or the unit of @x@ when there are none.
merges :: forall {s} (x :: s) pre. (Hypergraph s, Typeable x, Ob x) => Sorts pre -> Strictified pre '[x]
merges Nil = memptyS @x
merges (Cons @y Nil) = case eqTypeRep (typeRep @x) (typeRep @y) of
  P.Just HRefl -> obj1 @x
  P.Nothing -> P.error "readBack: a spider was planned on wires of other sorts"
merges (Cons @y rest@Cons{}) = case eqTypeRep (typeRep @x) (typeRep @y) of
  P.Just HRefl -> mappendS @x . (obj1 @x ** merges @x rest)
  P.Nothing -> P.error "readBack: a spider was planned on wires of other sorts"

-- | One wire of sort @x@ copied to @m@, or discarded when @m@ is 0.
copies :: forall {s} (x :: s). (Hypergraph s, Typeable x, Ob x) => P.Int -> Built '[x]
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
  -> Strictified (us ++ xs) (us ++ ys)
  -> Strictified xs ys
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
