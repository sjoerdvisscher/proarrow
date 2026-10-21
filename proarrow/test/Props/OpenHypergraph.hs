{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Open hypergraphs with wires sorted by objects of 'Mat'. Equality is 'isomorphic', so the laws
-- hold up to renaming nodes and reordering boxes, and the examples check that terms equal by the
-- Frobenius laws give isomorphic hypergraphs and that others do not.
module Props.OpenHypergraph (test) where

import Control.Monad (replicateM)
import Data.Kind (Constraint, Type)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as M
import Data.Type.Nat (Nat2, Nat3)
import Data.Universe.Class (Finite (..))
import Test.Falsify (Property, testFailed)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (elem, id, mappend, mempty, (**), (.))

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.FinHask (FINHASK (..), FinHask (..))
import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , Boxes (..)
  , OPENHG
  , Port (..)
  , SIMPLIFY
  , SomeArrow
  , SomeHypergraph (..)
  , SomeSort
  , Sorted
  , WireSorts
  , Wires
  , Wiring
  , box
  , copyDiscard
  , frobenius
  , frobeniusWith
  , isomorphic
  , layered
  , openHypergraph
  , permutations
  , prim
  , prim0
  , prim1
  , prim2
  , prim3
  , readBack
  , sameSort
  , simplify
  , simplifyFlat
  , simplifyHypergraph
  , someArrow
  , sortList
  , sortOf
  , substitute
  , substituteWith
  , tracedWith
  , unsafeOpenHypergraph
  )
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..))
import Proarrow.Category.Monoidal.Hypergraph (Hypergraph, Sized (..), cap, cup, traceHG)
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..), singleton)
import Proarrow.Core (Any, CAT, CategoryOf (..), Promonad (..), UN, obj)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Profunctor.Free (HasFreeK (..))
import Proarrow.Testing
  ( SomeOf (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , check
  , expect
  , genNamed
  , genSomeDef
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Proarrow.Tools.Diagrams.Svg (SVG (..), Svg (..), W (Wire), node, render)
import Proarrow.Tools.Diagrams.Svg qualified as Svg
import Proarrow.Tools.Einsum (einsum)
import Proarrow.Tools.SMC.Examples (hadamardT, matMulT, traceIdxT)
import Props.Mat ()
import Props.OpenHypergraph.Generated qualified as Generated
import Props.SMC (name)

type OH = OPENHG (MatK Int) String

-- | One wire of each sort.
type I = Wires '[M2] :: OH

type B = Wires '[M3] :: OH

-- The full SVG category with unequal sort sizes, to distinguish crossing count from cost.
type Weighted = SUBCAT (Any :: SVG -> Constraint)
type Large :: Weighted
type Large = SUB (S '[Wire "large"])
type Small :: Weighted
type Small = SUB (S '[Wire "small"])

instance Sized Weighted where
  sizeOf @(SUB (S ws)) = product [if wireLabel == "large" then 10 else 1 | (wireLabel, _) <- Svg.wires @ws]

weightedGate :: String -> Large ~> Small
weightedGate title = Sub (node @'[Wire "large"] @'[Wire "small"] title)

diagramParts :: Svg.Diagram -> [Svg.Diagram]
diagramParts = \case
  Svg.Seq a b -> diagramParts a ++ diagramParts b
  Svg.Beside a b -> diagramParts a ++ diagramParts b
  Svg.Trace _ d -> diagramParts d
  d -> [d]

boxNames :: Svg.Diagram -> [String]
boxNames diagram = [title | Svg.Node _ title _ _ <- diagramParts diagram]

wireCrossings :: Svg.Diagram -> Int
wireCrossings diagram =
  sum [length (filter (< i) rest) | Svg.Permute _ _ positions <- diagramParts diagram, i : rest <- List.tails positions]

test :: TestTree
test =
  testGroup
    "Open hypergraphs"
    [ Generated.test
    , testCategory @OH
    , testDagger @OH
    , testMonoidal_ @OH
    , testSymMonoidal_ @OH
    , testClosed_ @OH
    , testDialogue_ @OH
    , testStarAutonomous_ @OH
    , testIsoMix_ @OH
    , testCompactClosed_ @OH
    , testCopyDiscard_ @OH
    , testHypergraph_ @OH
    , testTraced_ @OH
    , testProperty "layered read-back tensors independent boxes" do
        let gate = node @'[Wire "a"] @'[Wire "a"] "f"
            graph = prim1 gate ** prim1 gate
        case (simplify permutations graph, simplify (layered permutations) graph) of
          (Right (Str (Svg _ serial)), Right (Str (Svg _ parallel))) ->
            check
              "independent boxes remain sequential"
              (Svg.layoutHeight (Svg.layout Svg.defaultOptions parallel) < Svg.layoutHeight (Svg.layout Svg.defaultOptions serial))
          _ -> testFailed "independent boxes could not be read back"
    , testProperty "read-back keeps carried wires beside and between gates" do
        let gate title = prim1 (node @'[Wire "a"] @'[Wire "a"] title)
            left = gate "g" . gate "f"
            right = gate "j" . gate "i"
            checkLayout :: Wiring SVG -> (a :: SIMPLIFY SVG) ~> b -> Property ()
            checkLayout wiring graph = case simplify wiring graph of
              Left err -> testFailed err
              Right (Str (Svg _ diagram)) -> expect "unnecessary crossings" 0 (wireCrossings diagram)
        sequence_
          [ do
              checkLayout wiring (left ** gate "h")
              checkLayout wiring (left ** gate "h" ** right)
              checkLayout wiring ((left . left . left) ** gate "h" ** (right . right))
          | base <- [permutations, copyDiscard, frobenius]
          , wiring <- [base, layered base]
          ]
    , testProperty "layered read-back prefers crossing small wires" do
        -- Both orders need one crossing. Crossing the inputs costs 100; crossing the outputs
        -- costs 1. List g first so unweighted tie-breaking would retain the expensive order.
        let graph =
              (prim1 (weightedGate "g") ** prim1 (weightedGate "f"))
                . swap @(SIMPLIFY Weighted) @(Wires '[Large]) @(Wires '[Large])
        case simplify (layered permutations) graph of
          Left err -> testFailed err
          Right (Str (Sub (Svg _ diagram))) -> expect "weighted box order" ["f", "g"] (boxNames diagram)
    , testProperty "Frobenius read-back preserves custom swap weights" do
        let gate title = prim1 (node @'[Wire "large"] @'[Wire "small"] title)
            graph =
              (gate "g" ** gate "f")
                . swap @(SIMPLIFY SVG) @(Wires '[S '[Wire "large"]]) @(Wires '[S '[Wire "large"]])
            -- SVG's Sized weights are uniform. These weights favor crossing after both boxes.
            custom = frobeniusWith (\s -> if sameSort s (Some @(S '[Wire "large"])) then 10 else 1)
            afterBox = takeWhile (\case Svg.Node{} -> False; _ -> True) . reverse
            checkWeights :: Wiring SVG -> Int -> Property ()
            checkWeights wiring expected = case simplify wiring graph of
              Left err -> testFailed err
              Right (Str (Svg _ diagram)) ->
                expect "crossing after the last box" expected (sum (map wireCrossings (afterBox (diagramParts diagram))))
        sequence_
          [ checkWeights wiring expected
          | (wiring, expected) <- [(frobenius, 0), (layered frobenius, 0), (custom, 1), (layered custom, 1)]
          ]
    , testProperty "state contraction routing removes crossings" do
        let graph :: Either String ((Wires '[] :: OPENHG SVG String) ~> Wires '[A, A])
            graph =
              openHypergraph
                (replicate 3 (Some @A))
                []
                [0, 1]
                [Box "A" [] [2, 0, 1], Box "B" [] [0, 1, 2], Box "C" [] [0, 2, 0]]
            state :: String -> SomeArrow SVG
            state title = someArrow @'[] @'[A, A, A] (Str (node @'[Svg.I] @'[Wire "A", Wire "A", Wire "A"] title))
        case graph >>= readBack frobenius state of
          Left err -> testFailed err
          Right (Str (Svg _ diagram)) -> do
            -- The previous boundary orders needed ten crossings in the same ((A,B),C) tree.
            expect "crossings" 8 (wireCrossings diagram)
            expect "tensor order" ["A", "B", "C"] (boxNames diagram)
    , testGroup
        "the Frobenius laws"
        [ testProperty "matrix multiplication in index notation is composition" $
            check "not isomorphic" (isomorphic (matMulT f h) (h . f))
        , testProperty "the trace in index notation is the cap after the cup" $
            check "not isomorphic" (isomorphic (traceIdxT g) (cap @I . (g ** obj @I) . cup @I))
        , testProperty "the entrywise product in index notation is mappend after the two after comult" $
            check "not isomorphic" (isomorphic (hadamardT f f') (mappend @B . (f ** f') . comult @I))
        , testProperty "speciality: copying then merging is the identity" $
            check "not isomorphic" (isomorphic (mappend @I . comult @I) id)
        , testProperty "a closed loop is not the empty diagram" $
            check "isomorphic" (not (isomorphic (counit @I . mempty @I) id))
        , testProperty "closed loops of different sorts differ" $
            check "isomorphic" (not (isomorphic (counit @I . mempty @I) (counit @B . mempty @B)))
        , testProperty "composition is not commutative" $
            check "isomorphic" (not (isomorphic (g . g') (g' . g)))
        , testProperty "einsum ij,jk is composition" $
            check "not isomorphic" (isomorphic (unStr (einsum @"ij,jk" (name f) (name h))) (unStr (name (h . f))))
        ]
    , testGroup
        "substitution"
        [ testProperty "identity substitution" $ do
            actual <- substituteOr (\x -> if x == "f" then SomeHypergraph f else SomeHypergraph h) (h . f)
            expectGraph "same diagram" (h . f) actual
        , testProperty "substitution composes" $ do
            let twice x = SomeHypergraph (box @_ @'[M2] @'[M2] x . box @_ @'[M2] @'[M2] x)
            first <- substituteOr twice g
            actual <- substituteOr twice first
            direct <- substituteOr (\_ -> SomeHypergraph (g . g . g . g)) g
            expectGraph "two stages" direct actual
        , testProperty "preserves composition" $ do
            let replace _ = SomeHypergraph (g' . g')
            actual <- substituteOr replace (g . g)
            single <- substituteOr replace g
            expectGraph "composition" (single . single) actual
        , testProperty "preserves tensor" $ do
            let replace _ = SomeHypergraph (g' . g')
            actual <- substituteOr replace (g ** g)
            single <- substituteOr replace g
            expectGraph "tensor" (single ** single) actual
        , testProperty "identity replacement merges nodes" $ do
            actual <- substituteOr (\_ -> SomeHypergraph (obj @I)) (g . g)
            expectGraph "identity" (obj @I) actual
        , testProperty "repeated ports and shared nodes" $ do
            actual <- substituteOr (\_ -> SomeHypergraph (obj @I)) (hadamardT g g)
            expectGraph "special Frobenius algebra" (obj @I) actual
        , testProperty "copy and discard replacements" $ do
            let copy = box @_ @'[M2] @'[M2, M2] "copy"
                discard = box @_ @'[M2] @'[] "drop"
                replace x = if x == "copy" then SomeHypergraph (comult @I) else SomeHypergraph (counit @I)
            actual <- substituteOr replace ((obj @I ** discard) . copy)
            expectGraph "counit law" (rightUnitorInv @OH @I) actual
        , testProperty "feedback becomes an isolated loop" $ do
            actual <- substituteOr (\_ -> SomeHypergraph (obj @I)) (traceIdxT g)
            expectGraph "closed loop" (counit @I . mempty @I) actual
        , testProperty "replacement keeps isolated nodes" $ do
            let loop = counit @I . mempty @I
            actual <- substituteOr (\_ -> SomeHypergraph (g ** loop)) g
            expectGraph "loop beside box" (g ** loop) actual
        , testProperty "rejects a different arity" $
            expectFailure "arity" (substitute (\_ -> SomeHypergraph (comult @I)) g)
        , testProperty "rejects a different sort" $
            expectFailure "sorts" (substitute (\_ -> SomeHypergraph (obj @B)) g)
        , testProperty "empty diagrams keep their nodes" $ do
            let graph = counit @I . mempty @I
            actual <- substituteOr (\_ -> error "no boxes") graph
            expectGraph "closed loop" graph actual
        , testProperty "circuit expansion commutes with interpretation" $ do
            hm <- genNamed @(M2 ~> M2) "H"
            zm <- genNamed @(M2 ~> M2) "Z"
            let gate x = box @_ @'[M2] @'[M2] x
                circuit = gate "X" . gate "H"
                expand x = SomeHypergraph (if x == "X" then gate "H" . gate "Z" . gate "H" else gate x)
                interpret x = someArrow (singleton (case x of "H" -> hm; "Z" -> zm; _ -> hm . zm . hm))
            expanded <- substituteOr expand circuit
            expectGraph "H-Z-H decomposition" (gate "H" . gate "Z" . gate "H" . gate "H") expanded
            before <- readBackOr interpret circuit
            after <- readBackOr interpret expanded
            expect "same matrix" (unMat before) (unMat after)
        , testProperty "replacement labels can have a different type" $ do
            actual <- substituteOr (\_ -> SomeHypergraph (box @Int @'[M2] @'[M2] 1)) g
            expectGraph "relabelled box" (box @Int @'[M2] @'[M2] 1) actual
        , testProperty "nullary boxes can add a closed component" $ do
            let emptyBox = box @_ @'[] @'[] "loop"
            actual <- substituteOr (\_ -> SomeHypergraph (counit @I . mempty @I)) emptyBox
            expectGraph "closed component" (counit @I . mempty @I) actual
        , testProperty "separate replacement nodes remain separate" $ do
            let replacement = unsafeOpenHypergraph @String @'[M2] @'[M2] (sortList @_ @'[M2, M2]) [0] [1] []
            actual <- substituteOr (\_ -> SomeHypergraph replacement) g
            expectGraph "discard then create" (mempty @I . counit @I) actual
        ]
    , testGroup
        "sort expansion"
        [ testProperty "singleton expansion agrees with substitution" $ do
            let replace x = if x == "f" then SomeHypergraph f else SomeHypergraph h
            expected <- substituteOr replace (h . f)
            expectExpanded expected (substituteWith (: []) replace (h . f))
        , testProperty "empty expansion removes wires but keeps boxes" $
            expectExpanded
              (emptyGate "g" . emptyGate "g")
              (substituteWith (const []) (SomeHypergraph . emptyGate) (g . g))
        , testProperty "empty expansion removes isolated loops" $
            expectExpanded
              (obj @(Unit :: OH))
              (substituteWith (const []) (\_ -> error "no boxes") (counit @I . mempty @I))
        , testProperty "multiple wires preserve composition" $
            expectExpanded
              (pairGate "g" . pairGate "g")
              (substituteWith pairSorts (SomeHypergraph . pairGate) (g . g))
        , testProperty "multiple wires preserve tensor" $
            expectExpanded
              (pairGate "g" ** pairGate "g'")
              (substituteWith pairSorts (SomeHypergraph . pairGate) (g ** g'))
        , testProperty "expanded copies keep boundary order" $
            expectExpanded
              (comult @(I ** B))
              (substituteWith pairSorts (\_ -> error "no boxes") (comult @I))
        , testProperty "expanded repeated ports share their nodes" $
            expectExpanded
              (hadamardT (pairGate "g") (pairGate "g"))
              (substituteWith pairSorts (SomeHypergraph . pairGate) (hadamardT g g))
        , testProperty "feedback expands into two loops" $
            expectExpanded
              (traceIdxT (pairGate "g"))
              (substituteWith pairSorts (SomeHypergraph . pairGate) (traceIdxT g))
        , testProperty "isolated nodes expand independently" $
            expectExpanded
              (counit @(I ** B) . mempty @(I ** B))
              (substituteWith pairSorts (\_ -> error "no boxes") (counit @I . mempty @I))
        , testProperty "sorts can expand to different lengths" $
            let mapSort s = if sameSort s (Some @M2) then sortList @_ @'[M2, M3] else []
                fi = box @_ @'[M2, M3] @'[] "f"
                hi = box @_ @'[] @'[M2, M3] "h"
                replace x = if x == "f" then SomeHypergraph fi else SomeHypergraph hi
            in expectExpanded (hi . fi) (substituteWith mapSort replace (h . f))
        , testProperty "rejects replacement arity before expansion" $
            expectFailure "arity" (substituteWith pairSorts (\_ -> SomeHypergraph g) g)
        , testProperty "rejects replacement sort order" $
            expectFailure
              "sorts"
              (substituteWith pairSorts (\_ -> SomeHypergraph (box @_ @'[M3, M2] @'[M3, M2] "g")) g)
        , testProperty "can change the kind of sorts" $
            expectExpanded
              (box @String @'[A] @'[A] "g")
              ( substituteWith
                  (const [Some @A])
                  (\x -> SomeHypergraph (box @String @'[A] @'[A] x))
                  g
              )
        ]
    , testGroup
        "symmetric monoidal read-back"
        [ testProperty "composition agrees with hypergraph read-back" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            hm <- genNamed @(M3 ~> M2) "h"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton hm)
            expectReadBack permutations interp (h . f)
        , testProperty "parallel boxes agree with hypergraph read-back" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            expectReadBack permutations (const (someArrow (singleton fm))) (f ** f)
        , testProperty "permutations need no boxes" $
            case readBack permutations (\_ -> error "no boxes") (swap @OH @I @B) of
              Left err -> testFailed err
              Right (Str actual) -> expect "swap" (unMat (swap @(MatK Int) @M2 @M3)) (unMat actual)
        , testProperty "nullary boxes and scalar components" $
            let state = box @String @'[] @'[M2] "state"
                finish = box @String @'[M2] @'[] "finish"
                scalar = box @String @'[] @'[] "scalar"
                interp x = case x of
                  "state" -> someArrow @'[] @'[M2] (Str (mempty @M2))
                  "finish" -> someArrow @'[M2] @'[] (Str (counit @M2))
                  _ -> someArrow @'[] @'[] (Str (obj @(Unit :: MatK Int)))
            in case readBack permutations interp ((finish . state) ** scalar) of
                 Left err -> testFailed err
                 Right (Str actual) -> expect "scalar" (unMat (counit @M2 . mempty @M2)) (unMat actual)
        , testProperty "rejects copying" $
            expectFailure "consumers" (readBack permutations (\_ -> error "no boxes") (comult @I))
        , testProperty "rejects merging" $
            expectFailure "producer" (readBack permutations (\_ -> error "no boxes") (mappend @I))
        , testProperty "rejects discarding" $
            expectFailure "consumers" (readBack permutations (\_ -> error "no boxes") (counit @I))
        , testProperty "rejects isolated loops" $
            expectFailure "isolated" (readBack permutations (\_ -> error "no boxes") (counit @I . mempty @I))
        , testProperty "rejects a directed cycle" $
            expectFailure "trace" (readBack permutations (const (someArrow (singleton (obj @M2)))) (traceIdxT g))
        , testProperty "rejects an ill-typed box" $
            expectFailure "box" (readBack permutations (const (someArrow (singleton (obj @M2)))) f)
        , testProperty "empty graph reads back as the unit identity" $
            case readBack permutations (\_ -> error "no boxes") (obj @(Unit :: OH)) of
              Left err -> testFailed err
              Right (Str actual) -> expect "unit" (unMat (obj @(Unit :: MatK Int))) (unMat actual)
        ]
    , testGroup
        "copy-discard read-back"
        [ testProperty "sharing between boxes agrees with hypergraph read-back" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            hm <- genNamed @(M3 ~> M2) "h"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton hm)
            expectReadBack copyDiscard interp ((h ** h) . comult @B . f)
        , testProperty "repeated inputs release a box only when all are available" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            let source = box @String @'[M2] @'[M2] "source"
                join = box @String @'[M2, M2] @'[M2] "join"
                -- Put the dependent box first in the graph's box list.
                graph =
                  unsafeOpenHypergraph @String @'[M2] @'[M2]
                    (sortList @_ @'[M2, M2, M2])
                    [0]
                    [2]
                    [Box "join" [1, 1] [2], Box "source" [0] [1]]
                interp x = if x == "source" then someArrow (singleton gm) else someArrow @'[M2, M2] @'[M2] (Str (mappend @M2))
            expectGraph "dependent box first" (join . comult @I . source) graph
            expectReadBack copyDiscard interp graph
        , testProperty "a shared node survives until its last consumer" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            expectReadBack copyDiscard (const (someArrow (singleton gm))) ((g ** g) . comult @I)
        , testProperty "a node can feed a box and an output boundary" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            expectReadBack copyDiscard (const (someArrow (singleton gm))) ((obj @I ** g) . comult @I)
        , testProperty "unused box outputs are discarded without removing the box" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            expectReadBack copyDiscard (const (someArrow (singleton gm))) (counit @I . g)
        , testProperty "unused box output is discarded before a later box" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            expectReadBack copyDiscard (const (someArrow (singleton gm))) ((counit @I . g) ** g)
        , testProperty "unused boundary inputs are discarded" $
            expectReadBack copyDiscard (\_ -> error "no boxes") (obj @I ** counit @B)
        , testProperty "repeated output ports are copied and permuted" $
            expectReadBack
              copyDiscard
              (\_ -> error "no boxes")
              ( unsafeOpenHypergraph @String @'[M2, M3] @'[M3, M2, M3, M2, M2]
                  (sortList @_ @'[M2, M3])
                  [0, 1]
                  [1, 0, 1, 0, 0]
                  []
              )
        , testProperty "nullary boxes can produce shared values" $
            let state = box @String @'[] @'[M2] "state"
            in expectReadBack copyDiscard (const (someArrow @'[] @'[M2] (Str (mempty @M2)))) (comult @I . state)
        , testProperty "empty graph" $
            expectReadBack copyDiscard (\_ -> error "no boxes") (obj @(Unit :: OH))
        , testProperty "rejects merging" $
            expectFailure "producer" (readBack copyDiscard (\_ -> error "no boxes") (mappend @I))
        , testProperty "rejects a node without a producer" $
            expectFailure "producer" (readBack copyDiscard (\_ -> error "no boxes") (mempty @I))
        , testProperty "rejects isolated nodes" $
            expectFailure "isolated" (readBack copyDiscard (\_ -> error "no boxes") (counit @I . mempty @I))
        , testProperty "rejects cycles" $
            expectFailure "trace" (readBack copyDiscard (const (someArrow (singleton (obj @M2)))) (traceIdxT g))
        , testProperty "rejects an ill-typed box" $
            expectFailure "box" (readBack copyDiscard (const (someArrow (singleton (obj @M2)))) f)
        , testProperty "primitive arities compose with ordered ports in a non-strict category" $
            let graph :: (Wires '[Int, Bool, Char] :: SIMPLIFY Type) ~> Wires '[String]
                graph =
                  prim3 (\((n, text), suffix) -> show (n :: Int) ++ text ++ suffix)
                    . (prim2 (\(n, b) -> if b then n + 1 else n - 1) ** prim1 (: []) ** prim0 (const "done"))
            in case simplify permutations graph of
                 Left err -> testFailed err
                 Right (Str actual) -> do
                   expect "true branch and port order" "4!done" (actual (3, (True, '!')))
                   expect "false branch and port order" "2?done" (actual (3, (False, '?')))
        , testProperty "primitive graph executes as a Haskell function with sharing" $
            let inc = prim1 ((+ 1) :: Int -> Int)
                add = prim2 (uncurry (+) :: (Int, Int) -> Int)
            in case simplify copyDiscard (add . comult . inc) of
                 Left err -> testFailed err
                 Right (Str actual) -> expect "shared result" 16 (actual 7)
        ]
    , testGroup
        "independent feedback capability"
        [ testProperty "permutations with trace agree with hypergraph read-back" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            expectReadBack (tracedWith permutations) (const (someArrow (singleton gm))) (traceIdxT g)
        , testProperty "cuts a multi-box cycle" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            hm <- genNamed @(M3 ~> M2) "h"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton hm)
                graph = traceIdxT (h . f)
            expectReadBack (tracedWith permutations) interp graph
        , testProperty "disconnected cycles close independently" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            let interp = const (someArrow (singleton gm))
                graph = traceIdxT g ** traceIdxT g
            expectReadBack (tracedWith permutations) interp graph
        , testProperty "copying a feedback wire to an output" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            let graph =
                  unsafeOpenHypergraph @String @'[] @'[M2]
                    (sortList @_ @'[M2, M2])
                    []
                    [0]
                    [Box "g" [0] [1], Box "g" [1] [0]]
                interp = const (someArrow (singleton gm))
            expectReadBack (tracedWith copyDiscard) interp graph
        , testProperty "copying a producerless feedback wire to an output" $
            let graph = traceHG @I @(Unit :: OH) @I (comult @I . rightUnitor)
            in expectReadBack (tracedWith copyDiscard) (\_ -> error "no boxes") graph
        , testProperty "producerless feedback supplies a box input" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            let graph = g . traceHG @I @(Unit :: OH) @I (comult @I . rightUnitor)
            expectReadBack (tracedWith copyDiscard) (const (someArrow (singleton gm))) graph
        , testProperty "repeated cyclic inputs are copied" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            let graph =
                  unsafeOpenHypergraph @String @'[] @'[]
                    (sortList @_ @'[M2])
                    []
                    []
                    [Box "g" [0, 0] [0]]
                interp = const (someArrow @'[M2, M2] @'[M2] (Str (mappend @M2 . (gm ** gm))))
            expectReadBack (tracedWith copyDiscard) interp graph
        , testProperty "trace alone still rejects copying" $
            expectFailure "consumers" (readBack (tracedWith permutations) (\_ -> error "no boxes") (comult @I))
        , testProperty "trace alone rejects a producerless state" $
            expectFailure "producer" (readBack (tracedWith permutations) (\_ -> error "no boxes") (mempty @I))
        , testProperty "traced copying still rejects merging" $
            expectFailure "producer" (readBack (tracedWith copyDiscard) (\_ -> error "no boxes") (mappend @I))
        , testProperty "isolated loop is a traced identity" $
            case readBack (tracedWith permutations) (\_ -> error "no boxes") (counit @I . mempty @I) of
              Left err -> testFailed err
              Right (Str actual) -> expect "dimension" (unMat (counit @M2 . mempty @M2)) (unMat actual)
        , testProperty "tracedWith replaces Frobenius feedback" $
            let d = node @'[Wire "A"] @'[Wire "A"] "g"
                graph = traceIdxT (box @_ @'[A] @'[A] "g") :: Wires '[] ~> (Wires '[] :: OPENHG SVG String)
            in case readBack (tracedWith frobenius) (const (someArrow (singleton d))) graph of
                 Left err -> testFailed err
                 Right (Str (Svg _ diagram)) -> check "target trace is missing" ("Trace " `List.isInfixOf` show diagram)
        , testProperty "Frobenius wiring reads an acyclic graph" $ do
            gm <- genNamed @(M2 ~> M2) "g"
            let graph = hadamardT g g
                interp = const (someArrow (singleton gm))
            expectReadBack frobenius interp graph
        , testProperty "Haskell feedback without copying" $
            case simplify (tracedWith permutations) productiveLoop of
              Left err -> testFailed err
              Right (Str actual) -> expect "productive loop" 21 (actual 7)
        , testProperty "Haskell feedback combined with copying" $
            case simplify (tracedWith copyDiscard) (comult . productiveLoop) of
              Left err -> testFailed err
              Right (Str actual) -> expect "shared loop result" (21, 21) (actual 7)
        ]
    , testGroup
        "read-back in Mat Int"
        [ testProperty "free hypergraph retraction preserves shared inputs" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            let lifted = liftK @CategoryOf @Hypergraph fm
                graph = (lifted ** lifted) . comult @(Wires '[M2])
                actual = retractK @CategoryOf @Hypergraph @(MatK Int) graph
            expect "retracted matrix" (unMat ((fm ** fm) . comult @M2)) (unMat actual)
        , testProperty "rejects a box with other sorts" $
            expectFailure "sorts" (readBack frobenius (const (someArrow (singleton (obj @M2)))) f)
        , testProperty "matrix multiplication in index notation reads back as composition (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M3 ~> M2) "g"
            let Str m = simplifyHypergraph (matMulT (prim1 fm) (prim1 gm))
            check "differs from g . f" (unMat m == unMat (gm . fm))
        , testProperty "the trace reads back as the trace (3)" $ do
            gm <- genNamed @(M3 ~> M3) "g"
            m <- readBackOr (\_ -> someArrow (singleton gm)) (traceIdxT (box @_ @'[M3] @'[M3] "g"))
            check "differs" (unMat m == unMat (traceIdxT gm))
        , testProperty "the entrywise product reads back as the entrywise product (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M2 ~> M3) "g"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton gm)
            m <- readBackOr interp (hadamardT (box @_ @'[M2] @'[M3] "f") (box @_ @'[M2] @'[M3] "g"))
            check "differs" (unMat m == unMat (hadamardT fm gm))
        , testProperty "einsum ij,jk reads back as the name of the composite (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M3 ~> M2) "g"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton gm)
            m <-
              readBackOr
                interp
                (unStr (einsum @"ij,jk" (name (box @String @'[M2] @'[M3] "f")) (name (box @String @'[M3] @'[M2] "g"))))
            check "differs" (unMat m == unMat ((obj @M2 ** (gm . fm)) . cup @M2))
        , testProperty "a node made in two layers is merged, not discarded (2, 3)" $ do
            am <- genNamed @(Unit ~> M3) "a"
            hm <- genNamed @(Unit ~> M2) "h"
            gm <- genNamed @(M2 ~> M3) "g"
            let interp x = case x of
                  "a" -> someArrow @'[] @'[M3] (Str am)
                  "h" -> someArrow @'[] @'[M2] (Str hm)
                  _ -> someArrow (singleton gm)
            m <-
              readBackOr
                interp
                ( cap @(Wires '[M3])
                    . (box @_ @'[] @'[M3] "a" ** (box @_ @'[M2] @'[M3] "g" . box @_ @'[] @'[M2] "h"))
                )
            check "differs" (unMat m == unMat (cap @M3 . (am ** (gm . hm)) . leftUnitorInv))
        , testProperty "two states merged, then a box on the merge (2, 3)" $ do
            am <- genNamed @(Unit ~> M3) "a"
            bm <- genNamed @(Unit ~> M3) "b"
            gm <- genNamed @(M3 ~> M2) "g"
            let interp x = case x of
                  "a" -> someArrow @'[] @'[M3] (Str am)
                  "b" -> someArrow @'[] @'[M3] (Str bm)
                  _ -> someArrow (singleton gm)
            m <-
              readBackOr
                interp
                (box @_ @'[M3] @'[M2] "g" . mappend @(Wires '[M3]) . (box @_ @'[] @'[M3] "a" ** box @_ @'[] @'[M3] "b"))
            check "differs" (unMat m == unMat (gm . mappend @M3 . (am ** bm) . leftUnitorInv))
        , testProperty "a closed loop reads back as the dimension (3)" $ do
            m <- readBackOr (\_ -> error "no boxes") (counit @(Wires '[M3] :: OM) . mempty @(Wires '[M3]))
            check "not 3" (unMat m == unMat (counit @M3 . mempty @M3))
        ]
    , testGroup
        "flat read-back in Mat Int, every box bent into a state"
        [ testProperty "matrix multiplication in index notation is composition (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M3 ~> M2) "g"
            let Str m = simplifyFlat (matMulT (prim1 fm) (prim1 gm))
            check "differs from g . f" (unMat m == unMat (gm . fm))
        , testProperty "the trace, a cycle, needs no trace (3)" $ do
            gm <- genNamed @(M3 ~> M3) "g"
            let Str m = simplifyFlat (traceIdxT (prim1 gm))
            check "differs" (unMat m == unMat (traceIdxT gm))
        , testProperty "the entrywise product (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M2 ~> M3) "g"
            let Str m = simplifyFlat (hadamardT (prim1 fm) (prim1 gm))
            check "differs" (unMat m == unMat (hadamardT fm gm))
        , testProperty "two states merged, then a box on the merge (2, 3)" $ do
            am <- genNamed @(Unit ~> M3) "a"
            bm <- genNamed @(Unit ~> M3) "b"
            gm <- genNamed @(M3 ~> M2) "g"
            let Str m =
                  simplifyFlat
                    ( prim1 gm
                        . mappend @(Wires '[M3])
                        . (prim0 am ** prim0 bm)
                    )
            check "differs" (unMat m == unMat (gm . mappend @M3 . (am ** bm) . leftUnitorInv))
        ]
    , testGroup
        "read-back in SVG"
        [ testProperty "matrix multiplication in index notation reads back with no points" $ do
            let d = node @'[Wire "A"] @'[Wire "A"] "f"
                t = matMulT (box @_ @'[A] @'[A] "f") (box @_ @'[A] @'[A] "f") :: Wires '[A] ~> (Wires '[A] :: OPENHG SVG String)
            case readBack frobenius (\_ -> someArrow (singleton d)) t of
              Right (Str r) -> check "points are drawn" (points (render r) == 0)
              Left e -> testFailed e
        , testProperty "the trace reads back with one spider on each side of the loop" $ do
            let d = node @'[Wire "A"] @'[Wire "A"] "h"
            case readBack
              frobenius
              (\_ -> someArrow (singleton d))
              (traceIdxT (box @_ @'[A] @'[A] "h") :: Wires '[] ~> (Wires '[] :: OPENHG SVG String)) of
              Right (Str r) -> check "not four points" (points (render r) == 4)
              Left e -> testFailed e
        ]
    ]
  where
    points = length . filter ("<circle" `List.isPrefixOf`) . List.tails
    f = box @_ @'[M2] @'[M3] "f"
    f' = box @_ @'[M2] @'[M3] "f'"
    h = box @_ @'[M3] @'[M2] "h"
    g = box @_ @'[M2] @'[M2] "g"
    g' = box @_ @'[M2] @'[M2] "g'"

type M2 = M Nat2 :: MatK Int
type M3 = M Nat3 :: MatK Int
type OM = OH
type A = S '[Wire "A"]

-- The feedback equation is u = n : u; only three elements are demanded for the result.
productiveLoop :: (Wires '[Int] :: SIMPLIFY Type) ~> Wires '[Int]
productiveLoop =
  traceHG @(Wires '[[Int]]) @(Wires '[Int]) @(Wires '[Int])
    (prim @'[[Int], Int] @'[[Int], Int] (Str (\(u, n) -> (n : u, sum (take 3 u)))))

pairSorts :: SomeSort (MatK Int) -> [SomeSort (MatK Int)]
pairSorts _ = sortList @_ @'[M2, M3]

pairGate :: String -> Wires '[M2, M3] ~> (Wires '[M2, M3] :: OH)
pairGate = box

emptyGate :: String -> Wires '[] ~> (Wires '[] :: OH)
emptyGate = box

expectExpanded
  :: forall {s} l as bs
   . (Eq l, DecidableIso s)
  => (Wires as :: OPENHG s l) ~> Wires bs
  -> Either String (SomeHypergraph s l)
  -> Property ()
expectExpanded expected@Objs result = case result of
  Left err -> testFailed err
  Right (SomeHypergraph (DecCospan @c (Sub (FinHask l)) (Sub (FinHask r)) (Boxes boxes))) ->
    let unPort (Port i) = i
    in case openHypergraph @l @as @bs
         (sortList @_ @(WireSorts (DC c)))
         (fmap unPort (M.elems l))
         (fmap unPort (M.elems r))
         (fmap (fmap unPort) boxes) of
         Left err -> testFailed err
         Right actual -> expectGraph "expanded diagram" expected actual

expectFailure :: String -> Either String a -> Property ()
expectFailure reason result = case result of
  Left err -> check ("wrong error: " ++ err) (reason `List.isInfixOf` err)
  Right _ -> testFailed ("expected an error about " ++ reason)

expectGraph :: forall {s} l a b. (Eq l, DecidableIso s) => String -> (a :: OPENHG s l) ~> b -> a ~> b -> Property ()
expectGraph message expected actual = check message (isomorphic expected actual)

substituteOr
  :: forall l a b
   . (String -> SomeHypergraph (MatK Int) l)
  -> (a :: OH) ~> b
  -> Property (Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG (MatK Int) l))
substituteOr replace graph = case substitute replace graph of
  Left err -> testFailed err
  Right result -> pure result

-- | The read-back in Mat Int as a matrix, failing the property if it fails.
readBackOr
  :: forall a b
   . (String -> SomeArrow (MatK Int))
  -> (a :: OM) ~> b
  -> Property (Fold (WireSorts a) ~> Fold (WireSorts b))
readBackOr interp t = case readBack frobenius interp t of
  Right (Str m) -> pure m
  Left e -> testFailed e

-- Compare against the full reader in a non-cartesian target: discarded boxes can still matter.
expectReadBack
  :: forall a b
   . Wiring (MatK Int)
  -> (String -> SomeArrow (MatK Int))
  -> (a :: OH) ~> b
  -> Property ()
expectReadBack wiring interp graph = do
  Mat values <- readBackOr interp graph
  case readBack wiring interp graph of
    Left err -> testFailed err
    Right (Str actual) -> expect "matrix" values (unMat actual)

instance Testable OH where
  showOb @a = "Wires " ++ show (fmap (\(Some @x) -> sizeOf @(MatK Int) @x) (sortList @(MatK Int) @(WireSorts a)))
  genSome =
    genSomeDef
      @'[ Wires '[]
        , Wires '[M2]
        , Wires '[M2, M3]
        , Wires '[M3, M3, M2]
        , Wires '[M3, M2, M2]
        ]

instance (Ob a, Ob b) => TestingEqShow (DecCospan a (b :: OH)) where
  eqP x y = pure (isomorphic x y)
  showP (DecCospan (Sub (FinHask l)) (Sub (FinHask r)) (Boxes bs)) =
    "DecCospan " ++ show l ++ " " ++ show r ++ " " ++ show bs

-- | A random apex from the palette, legs into it that keep the sorts of the ports, and up to two
-- boxes on its nodes.
instance (Ob a, Ob b) => TestableType (DecCospan a (b :: OH)) where
  gen = GenNonEmpty loop
    where
      loop = do
        c <- genSome @OH
        case c of
          Some @(DC (SUB (FH n))) -> do
            let nodesOfSort x = [y | y <- universeF @n, sameSort (sortOf @(MatK Int) @(FH n) y) x]
                leg :: forall p. (Sorted (MatK Int) (FH p)) => Maybe [(p, NonEmpty n)]
                leg =
                  traverse (\x -> case nodesOfSort (sortOf @(MatK Int) @(FH p) x) of [] -> Nothing; y : ys -> Just (x, y :| ys)) universeF
            case (leg @(UN FH (UN SUB (UN DC a))), leg @(UN FH (UN SUB (UN DC b)))) of
              (Just la, Just lb) -> do
                l <- traverse (\(x, ys) -> (x,) <$> elem ys) la
                r <- traverse (\(x, ys) -> (x,) <$> elem ys) lb
                bs <- case universeF @n of
                  [] -> pure []
                  n0 : ns -> do
                    k <- elem [0 .. 2]
                    replicateM k do
                      x <- elem ["f", "g"]
                      ni <- elem [0 .. 2]
                      no <- elem [0 .. 2]
                      Box x <$> replicateM ni (elem (n0 :| ns)) <*> replicateM no (elem (n0 :| ns))
                pure (DecCospan (Sub (FinHask (M.fromList l))) (Sub (FinHask (M.fromList r))) (Boxes bs))
              _ -> loop

instance TestableProfunctor (DecCospan :: CAT OH)
