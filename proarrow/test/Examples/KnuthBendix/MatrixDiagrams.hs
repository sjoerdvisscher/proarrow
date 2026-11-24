-- | Finite relations and matrices of natural numbers, with direct sum as
-- tensor. A merge's input legs and a split's output legs are unordered.
-- See <https://arxiv.org/abs/1601.02307 Coya and Fong> for finite relations.
module Examples.KnuthBendix.MatrixDiagrams (test) where

import Control.Monad (forM_)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List (sort, transpose)
import Data.Maybe (listToMaybe)
import Data.Type.Nat (Nat1, Nat2, Nat3)
import Data.Vec.Lazy qualified as V
import Numeric.Natural (Natural)
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((**), (.))

import Proarrow.Category.Enriched.Dagger (DaggerProfunctor (dagger))
import Proarrow.Category.Instance.FinRel (FINREL (FR), FinRel (..), toBools)
import Proarrow.Category.Instance.Mat (Mat (..), MatK (M))
import Proarrow.Category.Instance.OpenHypergraph (W1, W2, W3)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Monoidal (MonoidalProfunctor ((**)), SymMonoidal (swap))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts ((+++), (|||)))
import Proarrow.Colimit.Initial (HasInitialObject (initiate))
import Proarrow.Core (Promonad ((.)), obj, type (~>))
import Proarrow.Limit.Terminal (HasTerminalObject (terminate))
import Proarrow.Monoid qualified as Mon
import Proarrow.Testing (check, expect)
import Proarrow.Tools.HypergraphRewrite ((==>))
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion

data Generator = Merge | Split | Unit | Counit | MergeLeg | SplitLeg | Related | Pivot
  deriving (Eq)

type Diagram as bs = (HG.Wires as :: HG.OPENHG () Generator) ~> HG.Wires bs

type Wire = HG.Wires @() @Generator W1

wire :: Diagram W1 W1
wire = obj @Wire

mergeBox, splitBox, mergeLeg, splitLeg, connection :: Diagram W1 W1
mergeBox = HG.box Merge
splitBox = HG.box Split
mergeLeg = HG.box MergeLeg
splitLeg = HG.box SplitLeg
connection = HG.box Related

joinWires :: Diagram W2 W1
joinWires = Mon.mappend @Wire

copyWire :: Diagram W1 W2
copyWire = Mon.comult @Wire

-- A fresh hub holds the two identical legs. The legs remain separate boxes,
-- so the two boundary wires retain their distinct nodes.
merge :: Diagram W2 W1
merge = mergeBox . joinWires . (mergeLeg ** mergeLeg)

split :: Diagram W1 W2
split = (splitLeg ** splitLeg) . copyWire . splitBox

unit :: Diagram '[] W1
unit = HG.box Unit

counit :: Diagram W1 '[]
counit = HG.box Counit

crossing :: Diagram W2 W2
crossing = swap @_ @Wire @Wire

type Rule = R.Rule () Generator

leftUnit, rightCounit, special, interaction :: Either String Rule
leftUnit = merge . (unit ** wire) ==> wire
rightCounit = (wire ** counit) . split ==> wire
special = merge . split ==> wire
interaction = split . merge ==> distributed

distributed :: Diagram W2 W2
distributed = (merge ** merge) . (wire ** crossing ** wire) . (split ** split)

-- Associativity on unordered binary merges can cycle. This rule is used
-- only with a rewrite limit to demonstrate the cycle.
associativity :: Either String Rule
associativity = merge . (merge ** wire) ==> merge . (wire ** merge)

completedContractions :: Either String ([Rule], R.CompiledRules Int () Generator)
completedContractions = do
  rules <-
    sequence
      [ mergeLeg . mergeBox ==> wire
      , splitBox . splitLeg ==> wire
      ]
  result <- Completion.completeHypergraph 1 4 (\l r -> compare (measure l) (measure r)) rules
  case result of
    Completion.HypergraphComplete final compiled -> Right (final, compiled)
    Completion.HypergraphIncomplete _ (Completion.HypergraphUnorientable reason _) -> Left reason
    Completion.HypergraphIncomplete{} -> Left "could not complete the merge and split contractions"
  where
    measure g =
      let (_, _, _, boxes) = HG.hypergraphParts g
      in (length boxes, length (filter ((== Merge) . HG.label) boxes))

parallelConnectionRules :: Either String (R.CompiledRules () () Generator)
parallelConnectionRules = do
  parallel <- joinWires . (connection ** connection) . copyWire ==> connection
  R.compileReducingRules [((), parallel)]

mergeRelation :: FinRel (FR Nat2) (FR Nat1)
mergeRelation = obj @(FR Nat1) ||| obj @(FR Nat1)

mergeThreeRelation :: FinRel (FR Nat3) (FR Nat1)
mergeThreeRelation = mergeRelation ||| obj @(FR Nat1)

relationTable :: FinRel a b -> [[Bool]]
relationTable (FinRel rows) = map (V.toList . toBools) (V.toList rows)

-- Each Boolean matrix entry says whether an input can reach an output. Every
-- encoded box connects each input to each output, including the nullary unit
-- and counit, which contribute no edges.
diagramRelationTable :: (a :: HG.OPENHG () Generator) ~> b -> [[Bool]]
diagramRelationTable diagram = [map (`IS.member` reachable input) outs | input <- ins]
  where
    (_, ins, outs, boxes) = HG.hypergraphParts diagram
    edges = IM.fromListWith (++) [(input, HG.outputs box) | box <- boxes, input <- HG.inputs box]
    reachable input = visit IS.empty [input]
    visit seen [] = seen
    visit seen (n : pending)
      | IS.member n seen = visit seen pending
      | otherwise = visit (IS.insert n seen) (IM.findWithDefault [] n edges ++ pending)

data Reachability = Edge | Reached | Unreached
  deriving (Eq)

reachabilityRules :: Either String (R.CompiledRules () () Reachability)
reachabilityRules = do
  propagate <- markedEdge Reached Unreached ==> markedEdge Reached Reached
  R.compileRules [((), propagate)]
  where
    markedEdge :: Reachability -> Reachability -> (HG.Wires W2 :: HG.OPENHG () Reachability) ~> HG.Wires '[]
    markedEdge source target =
      HG.unsafeOpenHypergraph
        (HG.sortList @() @W2)
        [0, 1]
        []
        [HG.Box Edge [0] [1], HG.Box source [0] [], HG.Box target [1] []]

-- Each propagation replaces one Unreached marker. The reachable nodes are
-- exactly the markers left after normalisation, even in the presence of cycles.
normaliseRelation
  :: forall as bs. (HG.SortList as, HG.SortList bs) => Diagram as bs -> Either String (Diagram as bs)
normaliseRelation diagram = do
  compiled <- reachabilityRules
  let (nodes, ins, outs, boxes) = HG.hypergraphParts diagram
      edges = [HG.Box Edge [i] [o] | HG.Box _ inputs outputs <- boxes, i <- inputs, o <- outputs]
      row start =
        let tags = [HG.Box (if node == start then Reached else Unreached) [node] [] | node <- [0 .. length nodes - 1]]
            host = HG.unsafeOpenHypergraph @Reachability @'[] @bs nodes [] outs (edges ++ tags)
            (_, _, outputNodes, result) = HG.hypergraphParts (R.normalisedGraph (R.normalise R.unlimitedRewrites compiled host))
            reached = IS.fromList [node | HG.Box Reached [node] [] <- result]
        in map (`IS.member` reached) outputNodes
  pure (relationDiagram @as @bs (map row ins))

normaliseRelationByLaws
  :: forall as bs. (HG.SortList as, HG.SortList bs) => Diagram as bs -> Either String (Diagram as bs)
normaliseRelationByLaws diagram = do
  parallel <- parallelConnectionRules
  normaliseConnections (R.normalisedGraph . R.normalise R.unlimitedRewrites parallel) diagram

normaliseNatural :: (HG.SortList as, HG.SortList bs) => Diagram as bs -> Either String (Diagram as bs)
normaliseNatural diagram
  | all acyclic (stronglyConnComp [(i, i, IM.findWithDefault [] i edges) | i <- [0 .. length nodes - 1]]) =
      normaliseConnections id diagram
  | otherwise = Left "Mat Natural diagrams must be acyclic"
  where
    (nodes, _, _, boxes) = HG.hypergraphParts diagram
    edges = IM.fromListWith (++) [(i, HG.outputs box) | box <- boxes, i <- HG.inputs box]
    acyclic AcyclicSCC{} = True
    acyclic CyclicSCC{} = False

-- Flatten merges and splits, then distribute across each internal junction.
-- The caller chooses whether parallel connections are identified or counted.
normaliseConnections
  :: forall as bs
   . (HG.SortList as, HG.SortList bs)
  => (Diagram as bs -> Diagram as bs) -> Diagram as bs -> Either String (Diagram as bs)
normaliseConnections simplify diagram = do
  (_, contractions) <- completedContractions
  let (nodes, ins, outs, boxes) = HG.hypergraphParts (R.normalisedGraph (R.normalise R.unlimitedRewrites contractions diagram))
      inputSorts = HG.sortList @() @as
      outputSorts = HG.sortList @() @bs
      inputs = take (length ins) [length nodes ..]
      outputs = take (length outs) [length nodes + length ins ..]
      edges = [(i, o) | HG.Box _ from to <- boxes, i <- from, o <- to, i /= o]
      network =
        HG.unsafeOpenHypergraph (nodes ++ inputSorts ++ outputSorts) inputs outputs $
          [HG.Box Related [i] [o] | (i, o) <- zip inputs ins ++ edges ++ zip outs outputs]
      eliminate host = case filter (`IS.notMember` boundary) [0 .. length sorts - 1] of
        [] -> Right host
        junction : _ -> distributeJunction junction host >>= eliminate . simplify
        where
          (sorts, inputNodes, outputNodes, _) = HG.hypergraphParts host
          boundary = IS.fromList (inputNodes ++ outputNodes)
  eliminate (simplify network)

-- Instantiate distributivity at the arities of a junction. The rule's
-- interface is the set of its neighbours, so matching also checks that no
-- other box touches the junction being removed. The first pattern box marks
-- the selected junction so the matcher starts there. The replacement consumes
-- that marker along with the junction.
distributeJunction
  :: forall as bs. (HG.SortList as, HG.SortList bs) => Int -> Diagram as bs -> Either String (Diagram as bs)
distributeJunction junction host = HG.reifySorts neighbourSorts \ @ports -> do
  let patternBoxes = HG.Box Pivot [centre] [] : incident
      markedJunction = HG.unsafeOpenHypergraph @Generator @ports @'[] (neighbourSorts ++ [nodes !! junction]) interface [] patternBoxes
      distributedConnections = HG.unsafeOpenHypergraph @Generator @ports @'[] neighbourSorts interface [] shortcuts
  distribute <- markedJunction ==> distributedConnections
  maybe
    (Left "could not match the junction's complete neighbourhood")
    Right
    (listToMaybe (R.rewrites distribute markedHost))
  where
    (nodes, ins, outs, boxes) = HG.hypergraphParts host
    markedHost = HG.unsafeOpenHypergraph @Generator @as @bs nodes ins outs (HG.Box Pivot [junction] [] : boxes)
    predecessors = sort [i | HG.Box Related [i] [o] <- boxes, o == junction]
    successors = sort [o | HG.Box Related [i] [o] <- boxes, i == junction]
    neighbours = IS.toAscList (IS.fromList (predecessors ++ successors))
    neighbourSorts = map (nodes !!) neighbours
    interface = [0 .. length neighbours - 1]
    centre = length neighbours
    local = (IM.fromList (zip neighbours interface) IM.!)
    incident =
      [HG.Box Related [local i] [centre] | i <- predecessors]
        ++ [HG.Box Related [centre] [local o] | o <- successors]
    -- A shortcut from a node to itself adds no relation.
    shortcuts = [HG.Box Related [local i] [local o] | i <- predecessors, o <- successors, i /= o]

relationDiagram :: forall as bs. (HG.SortList as, HG.SortList bs) => [[Bool]] -> Diagram as bs
relationDiagram = connectionDiagram @as @bs . map (map (\related -> if related then 1 else 0))

-- The two boundaries contain distinct nodes. Each entry gives the number of
-- connections from its input to its output.
connectionDiagram :: forall as bs. (HG.SortList as, HG.SortList bs) => [[Natural]] -> Diagram as bs
connectionDiagram table = HG.unsafeOpenHypergraph (inputs ++ outputs) ins outs boxes
  where
    inputs = HG.sortList @() @as
    outputs = HG.sortList @() @bs
    ins = [0 .. length inputs - 1]
    outs = [length inputs .. length inputs + length outputs - 1]
    boxes = [HG.Box Related [i] [o] | (i, row) <- zip ins table, (o, count) <- zip outs row, _ <- [1 .. count]]

allBinaryRelations :: [FinRel (FR Nat2) (FR Nat2)]
allBinaryRelations = [FinRel (x V.::: y V.::: V.VNil) | x <- [minBound .. maxBound], y <- [minBound .. maxBound]]

mergeLeft :: Diagram W3 W1
mergeLeft = merge . (merge ** wire)

mergeRight :: Diagram W3 W1
mergeRight = merge . (wire ** merge)

feedback :: Diagram W1 W1
feedback =
  HG.unsafeOpenHypergraph
    (HG.sortList @() @W3)
    [0]
    [2]
    [HG.Box Related [0] [1], HG.Box Related [1] [0], HG.Box Related [1] [2]]

test :: TestTree
test = testGroup "Matrix diagrams" [relationTests, naturalTests]

relationTests :: TestTree
relationTests =
  testGroup
    "Finite relations with unordered ports"
    [ testProperty "swapping commutative ports gives isomorphic diagrams" $ do
        check "merge inputs are unordered" (HG.isomorphic merge (merge . crossing))
        check "split outputs are unordered" (HG.isomorphic split (crossing . split))
        check "the boundary is ordered" (not (HG.isomorphic (wire ** wire) crossing))
        expect "merge as a relation" (relationTable mergeRelation) (diagramRelationTable merge)
        expect "split as a relation" (relationTable (dagger mergeRelation)) (diagramRelationTable split)
    , testProperty "orienting associativity on unordered merges creates a rewrite cycle" $ do
        associate <- either testFailed pure associativity
        compiled <- either testFailed pure (R.compileRules [((), associate)])
        check "the merge trees differ" (not (HG.isomorphic mergeLeft mergeRight))
        check "there is a step back to the left-associated tree" $
          any (HG.isomorphic mergeLeft . snd) (R.rewritesCompiled compiled mergeRight)
        let result = R.normalise (R.RewriteLimits (Just 4) Nothing) compiled mergeLeft
        expect "the associativity rule keeps applying" R.RewriteLimitReached (R.normalisationStatus result)
    , testProperty "completion makes merge and split contractions converge" $ do
        (final, compiled) <- either testFailed pure completedContractions
        expect "one learned rule joins the two contractions" 3 (length final)
        let flatMerge = mergeBox . joinWires . (joinWires ** wire) . (mergeLeg ** mergeLeg ** mergeLeg)
            flatSplit = (splitLeg ** splitLeg ** splitLeg) . (copyWire ** wire) . copyWire . splitBox
            checkTree :: Diagram as bs -> [[Bool]] -> Diagram as bs -> Property ()
            checkTree flat expected tree = do
              let normal = R.normalise R.unlimitedRewrites compiled tree
              expect "one contraction" 1 (R.normalisationRewrites normal)
              expect "the flattened tree is irreducible" R.NormalForm (R.normalisationStatus normal)
              check "the tree flattens to one junction with three legs" (HG.isomorphic flat (R.normalisedGraph normal))
              expect "the flattened diagram has the same relation" expected (diagramRelationTable (R.normalisedGraph normal))
        forM_ [mergeLeft, mergeRight] (checkTree flatMerge (relationTable mergeThreeRelation))
        forM_
          [(split ** wire) . split, (wire ** split) . split]
          (checkTree flatSplit (relationTable (dagger mergeThreeRelation)))
    , testProperty "one rule matches either leg and both matches meet on a shared merge" $ do
        removeUnit <- either testFailed pure leftUnit
        compiled <- either testFailed pure (R.compileReducingRules [((), removeUnit)])
        forM_ [merge . (unit ** wire), merge . (wire ** unit)] \host ->
          case R.rewritesCompiled compiled host of
            [((), reduct)] -> check "the unit disappears" (HG.isomorphic wire reduct)
            _ -> testFailed "expected the same compiled rule to match either leg"
        peaks <- either testFailed pure (Completion.hypergraphOverlaps [((), removeUnit)])
        case [ HG.isomorphic left right
             | Completion.CriticalOverlap () () host left right <- peaks
             , let (_, _, _, boxes) = HG.hypergraphParts host
             , length (filter ((== Unit) . HG.label) boxes) == 2
             , length (filter ((== Merge) . HG.label) boxes) == 1
             ] of
          [] -> testFailed "expected an overlap between the two unit matches"
          joins -> check "the symmetric self-overlaps join" (and joins)
    , testProperty "the bimonoid interaction works in all port orders" $ do
        let host = crossing . split . merge . crossing
            expected = relationTable (dagger mergeRelation . mergeRelation)
        distribute <- either testFailed pure interaction
        compiled <- either testFailed pure (R.compileRules [((), distribute)])
        let reducts = map snd (R.rewritesCompiled compiled host)
        expect "two choices for each pair of ports" 4 (length reducts)
        expect "input diagram's bit matrix" expected (diagramRelationTable host)
        forM_ reducts \reduct -> do
          check "every choice gives the distributed diagram" (HG.isomorphic distributed reduct)
          expect "distributed diagram's bit matrix" expected (diagramRelationTable reduct)
    , testProperty "the special law collapses two paths to a single relation entry" $ do
        rules <- either testFailed pure (sequence [leftUnit, rightCounit, special])
        compiled <- either testFailed pure (R.compileReducingRules (zip [0 :: Int ..] rules))
        let host = merge . crossing . split . merge . (wire ** unit)
            expected = relationTable (mergeRelation . dagger mergeRelation)
            normal = R.normalise R.unlimitedRewrites compiled host
        expect "the original diagram represents the composite relation" expected (diagramRelationTable host)
        expect "two rewrites" 2 (R.normalisationRewrites normal)
        expect "normal form" R.NormalForm (R.normalisationStatus normal)
        check "the normal form is one wire" (HG.isomorphic wire (R.normalisedGraph normal))
        expect "the bit matrix is unchanged" expected (diagramRelationTable (R.normalisedGraph normal))
    , testProperty "normal forms agree with every composition of two by two relations" $
        forM_ [(left, right) | left <- allBinaryRelations, right <- allBinaryRelations] \(left, right) -> do
          let diagram relation = relationDiagram @W2 @W2 (relationTable relation)
              source = diagram right . diagram left
              expected = diagram (right . left)
          normal <- either testFailed pure (normaliseRelation source)
          byLaws <- either testFailed pure (normaliseRelationByLaws source)
          check ("normal form of " ++ show left ++ " followed by " ++ show right) (HG.isomorphic expected normal)
          check "distributivity and the special law give the same normal form" (HG.isomorphic normal byLaws)
    , testProperty "normal forms keep ordered ports, including shared ports and feedback" $ do
        let normalisesTo label source expected = do
              normal <- either testFailed pure (normaliseRelation source)
              byLaws <- either testFailed pure (normaliseRelationByLaws source)
              check label (HG.isomorphic expected normal)
              check (label ++ " also normalises using the laws") (HG.isomorphic expected byLaws)
        normalisesTo "identity" (wire ** wire) (relationDiagram @W2 @W2 [[True, False], [False, True]])
        normalisesTo "a swap" crossing (relationDiagram @W2 @W2 [[False, True], [True, False]])
        normalisesTo "duplicate paths and fan-out" (split . merge . split) (relationDiagram @W1 @W2 [[True, True]])
        normalisesTo "nested distributivity" (split . merge . split . merge) $
          relationDiagram @W2 @W2 (relationTable (dagger mergeRelation . mergeRelation))
        normalisesTo "three-wire trees and parallel paths" ((wire ** split) . split . merge . split . mergeLeft) $
          relationDiagram @W3 @W3 (relationTable (dagger mergeThreeRelation . mergeThreeRelation))
        normalisesTo "two output ports on one node" copyWire (relationDiagram @W1 @W2 [[True, True]])
        normalisesTo "feedback" feedback (relationDiagram @W1 @W1 [[True]])
        normalisesTo "empty source" unit (relationDiagram @'[] @W1 [])
        normalisesTo "empty target" counit (relationDiagram @W1 @'[] [[]])
    ]

-- Mat stores one row per output, whereas the diagrams are built input first.
matrixDiagram
  :: forall as bs (a :: MatK Natural) b. (HG.SortList as, HG.SortList bs) => Mat a b -> Diagram as bs
matrixDiagram (Mat rows) = connectionDiagram @as @bs (transpose (map V.toList (V.toList rows)))

checkMatrix
  :: forall as bs (a :: MatK Natural) b. (HG.SortList as, HG.SortList bs) => Mat a b -> Diagram as bs -> Property ()
checkMatrix expected source = do
  normal <- either testFailed pure (normaliseNatural source)
  check
    "each matrix entry gives the number of parallel connections"
    (HG.isomorphic (matrixDiagram @as @bs expected) normal)

mergeMatrix :: Mat (M Nat2 :: MatK Natural) (M Nat1)
mergeMatrix = obj @(M @Natural Nat1) ||| obj @(M @Natural Nat1)

binaryMatrices :: [Mat (M Nat2 :: MatK Natural) (M Nat2)]
binaryMatrices = [Mat (l V.::: r V.::: V.VNil) | l <- rows, r <- rows]
  where
    rows = [a V.::: b V.::: V.VNil | a <- [0, 1], b <- [0, 1]]

naturalTests :: TestTree
naturalTests =
  testGroup
    "Matrices of natural numbers"
    [ testProperty "parallel paths add multiplicities" $ do
        let splitMatrix = dagger mergeMatrix
            composite = mergeMatrix . splitMatrix
        case composite of
          Mat rows -> expect "two paths contribute 2" [[2]] (map V.toList (V.toList rows))
        checkMatrix composite (merge . split)
        checkMatrix (splitMatrix . composite . mergeMatrix) (split . merge . split . merge)
        let mergeThree = mergeMatrix ||| obj @(M @Natural Nat1)
        checkMatrix
          (dagger mergeThree . composite . mergeThree)
          ((wire ** split) . split . merge . split . mergeLeft)
    , testProperty "tensor uses block sum and the empty boundary has dimension zero" $ do
        checkMatrix (mergeMatrix +++ obj @(M @Natural Nat1)) (merge ** wire)
        checkMatrix (initiate @(MatK Natural) @(M Nat1)) unit
        checkMatrix (terminate @(MatK Natural) @(M Nat1)) counit
    , testProperty "normal forms agree with all compositions of two by two zero-one matrices" $
        forM_ [(left, right) | left <- binaryMatrices, right <- binaryMatrices] \(left, right) ->
          checkMatrix (right . left) (matrixDiagram @W2 @W2 right . matrixDiagram @W2 @W2 left)
    , testProperty "rectangular composition multiplies weighted entries" $ do
        let left :: Mat (M Nat2 :: MatK Natural) (M Nat2)
            left = Mat ((2 V.::: 1 V.::: V.VNil) V.::: (0 V.::: 3 V.::: V.VNil) V.::: V.VNil)
            right :: Mat (M Nat2 :: MatK Natural) (M Nat1)
            right = Mat ((4 V.::: 2 V.::: V.VNil) V.::: V.VNil)
        checkMatrix (right . left) (matrixDiagram @W2 @W1 right . matrixDiagram @W2 @W2 left)
    , testProperty "feedback falls outside finite path counting" $
        case normaliseNatural feedback of
          Left reason -> expect "cycle rejection" "Mat Natural diagrams must be acyclic" reason
          Right _ -> testFailed "expected a directed cycle to be rejected"
    ]
