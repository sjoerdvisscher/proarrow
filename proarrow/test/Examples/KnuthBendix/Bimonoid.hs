{-# OPTIONS_GHC -Wno-orphans #-}

-- | The ten oriented rules and 22 overlaps of the noncommutative bimonoid
-- example in <https://arxiv.org/html/2109.06049#S6.SS1 String Diagram Rewrite Theory III, §6.1>.
module Examples.KnuthBendix.Bimonoid (test) where

import Control.Monad (foldM, forM_, guard, join)
import Data.Bifunctor qualified as B
import Data.Fin (Fin, fin0, toNatural, universe)
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List (mapAccumL, permutations, sort)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy (Proxy (..))
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3)
import Data.Vec.Lazy qualified as V
import Test.Falsify (Property, testFailed)
import Test.Falsify qualified as Falsify
import Test.Falsify.Generator qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((**), (.))

import Proarrow.Category.Instance.Bimonoid (BIPATHS (..), Bimonoid, Wire, fromOrderedPaths, orderedPaths)
import Proarrow.Category.Instance.OpenHypergraph (W1, W2, W3)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.Simplex (IsNat (..), Nat (..), SNat (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (one, (**)), SymMonoidal (swap))
import Proarrow.Category.Monoidal.Strictified (pattern Str)
import Proarrow.Core (Ob, Promonad ((.)), UN, obj, (//), type (~>))
import Proarrow.Monoid qualified as Mon
import Proarrow.Object (SomeOf (..))
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow
  , check
  , expect
  , genSomeDef
  , optGen
  )
import Proarrow.Testing.Laws
  ( testCategory
  , testComonoid_
  , testDagger
  , testInitialObject
  , testMonoid_
  , testMonoidal_
  , testSymMonoidal_
  , testTerminalObject
  )
import Proarrow.Tools.HypergraphRewrite ((==>))
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion
import Proarrow.Tools.Laws (Equation, ProEquation ((:=:)), withSides)

data Generator = Multiply | Unit | Comultiply | Counit
  deriving (Eq, Show)

data Diagram = Diagram [Int] [Int] [HG.Box Generator Int]

type Graph :: [()] -> [()] -> Type
type Graph as bs = (HG.Wires as :: HG.OPENHG () Generator) ~> HG.Wires bs

multiply :: Graph W2 W1
multiply = HG.box Multiply

comultiply :: Graph W1 W2
comultiply = HG.box Comultiply

wire :: Graph W1 W1
wire = obj

unit :: Graph '[] W1
unit = HG.box Unit

counit :: Graph W1 '[]
counit = HG.box Counit

crossing :: Graph W2 W2
crossing = swap @(HG.OPENHG () Generator) @(HG.Wires W1) @(HG.Wires W1)

wireSorts :: Int -> [HG.SomeSort ()]
wireSorts n = replicate n (Some @'())

diagram :: (HG.SortList as, HG.SortList bs) => Diagram -> Graph as bs
diagram d@(Diagram ins outs boxes) = HG.unsafeOpenHypergraph (wireSorts (nodeCount d)) ins outs boxes

nodeCount :: Diagram -> Int
nodeCount (Diagram ins outs boxes) = 1 + maximum vertices
  where
    vertices = -1 : ins ++ outs ++ concatMap (\b -> HG.inputs b ++ HG.outputs b) boxes

diagramParts :: (a :: HG.OPENHG () Generator) ~> b -> Diagram
diagramParts hg = let (_, ins, outs, boxes) = HG.hypergraphParts hg in Diagram ins outs boxes

dual :: Diagram -> Diagram
dual (Diagram ins outs boxes) = Diagram outs ins (map dualBox boxes)

dualBox :: HG.Box Generator Int -> HG.Box Generator Int
dualBox (HG.Box g ins outs) = HG.Box (dualGenerator g) outs ins
  where
    dualGenerator Multiply = Comultiply
    dualGenerator Unit = Counit
    dualGenerator Comultiply = Multiply
    dualGenerator Counit = Unit

type NamedEquation = (String, Equation (HG.OPENHG () Generator))

rule :: NamedEquation -> Either String (String, R.Rule () Generator)
rule (name, equation) = (name,) <$> withSides equation (==>)

rules :: Either String [(String, R.Rule () Generator)]
rules = traverse rule equations

compiledRules :: Property (Completion.ConvexRules () Generator)
compiledRules = either testFailed pure (rules >>= Completion.compileConvexRules . map snd)

alternativeRules :: Either String [(String, R.Rule () Generator)]
alternativeRules = traverse rule (rightUnit : expandedInteraction : expandedRightCounit : filter otherEquation equations)
  where
    otherEquation (name, _) = name `notElem` ["right unit", "right counit", "multiplication and comultiplication"]

expandedInteraction :: NamedEquation
expandedInteraction = ("interaction with a right unit", expandedInteractionLeft :=: interactionRight)

expandedInteractionLeft :: Graph W2 W2
expandedInteractionLeft = comultiply . multiply . ((multiply . (wire ** unit)) ** wire)

rightUnit :: NamedEquation
rightUnit = ("right unit", multiply . (wire ** unit) :=: wire)

rightCounit :: NamedEquation
rightCounit = ("right counit", (wire ** counit) . comultiply :=: wire)

expandedRightCounit :: NamedEquation
expandedRightCounit =
  ("right counit with a right unit", multiply . (wire ** unit) . (wire ** counit) . comultiply :=: wire)

interaction :: NamedEquation
interaction = ("multiplication and comultiplication", comultiply . multiply :=: interactionRight)

interactionRight :: Graph W2 W2
interactionRight = (multiply ** multiply) . (wire ** crossing ** wire) . (comultiply ** comultiply)

equations :: [NamedEquation]
equations =
  [ ("associate", multiply . (multiply ** wire) :=: multiply . (wire ** multiply))
  , ("coassociate", (comultiply ** wire) . comultiply :=: (wire ** comultiply) . comultiply)
  , ("left unit", multiply . (unit ** wire) :=: wire)
  , rightUnit
  , ("left counit", (counit ** wire) . comultiply :=: wire)
  , rightCounit
  , ("multiplication preserves counit", counit . multiply :=: counit ** counit)
  , ("comultiplication preserves unit", comultiply . unit :=: unit ** unit)
  , interaction
  , ("counit preserves unit", counit . unit :=: one)
  ]

-- In the cartesian model on a free monoid, multiplication concatenates
-- words and comultiplication copies them. Each output is a word in the inputs.
readWords :: Diagram -> Maybe [[Int]]
readWords = fmap (map (map fst)) . readPaths

-- Each output lists its paths in merge order. A path is named by its input
-- and its position in that input's copy tree, both numbered from zero.
type OrderedPaths = [[(Int, Int)]]

interpretGenerator :: Generator -> HG.SomeArrow BIPATHS
interpretGenerator Multiply = HG.someArrow (Mon.mappendS @Wire)
interpretGenerator Unit = HG.someArrow (Mon.memptyS @Wire)
interpretGenerator Comultiply = HG.someArrow (Mon.comultS @Wire)
interpretGenerator Counit = HG.someArrow (Mon.counitS @Wire)

wireSort :: HG.SomeSort BIPATHS
wireSort = Some @Wire

interpretDiagram
  :: forall (as :: [BIPATHS]) (bs :: [BIPATHS])
   . (HG.SortList as, HG.SortList bs)
  => Diagram -> Either String (as ~> bs)
interpretDiagram d@(Diagram ins outs boxes) = do
  graph <- HG.openHypergraph @Generator @as @bs (replicate (nodeCount d) wireSort) ins outs boxes
  HG.readBack HG.permutations interpretGenerator graph

checkEquationSemantics :: String -> (a :: HG.OPENHG () Generator) ~> b -> a ~> b -> Property ()
checkEquationSemantics name l r =
  HG.reifySorts (replicate (length ins) wireSort) \ @as ->
    HG.reifySorts (replicate (length outs) wireSort) \ @bs -> do
      left <- either (testFailed . ((name ++ " left side: ") ++)) pure (interpretDiagram @as @bs lhs)
      right <- either (testFailed . ((name ++ " right side: ") ++)) pure (interpretDiagram @as @bs rhs)
      case (left, right) of
        (Str leftArrow, Str rightArrow) -> expect name leftArrow rightArrow
  where
    lhs@(Diagram ins outs _) = diagramParts l
    rhs = diagramParts r

instance Testable BIPATHS where
  genSome = genSomeDef @'[BP Nat0, BP Nat1, BP Nat2, BP Nat3]
  showOb @(BP a) = show (length (universe @a))

instance TestingEqShow (Bimonoid a b)
instance (Ob a, Ob b) => TestableType (Bimonoid a b) where
  gen =
    optGen
      [ arrow
      | paths <- smallPaths (universe @(UN BP a)) (length (universe @(UN BP b)))
      , Just arrow <- [toVec (singNat @(UN BP b)) paths >>= fromOrderedPaths]
      ]
instance TestableProfunctor Bimonoid

toVec :: SNat n -> [x] -> Maybe (V.Vec n x)
toVec SZ [] = Just V.VNil
toVec (SS @n) (x : xs) = (x V.:::) <$> toVec (singNat @n) xs
toVec _ _ = Nothing

pathsFromLists :: forall a b. (IsNat a, IsNat b) => OrderedPaths -> Maybe (Bimonoid (BP a) (BP b))
pathsFromLists paths = do
  fibres <- toVec (singNat @b) paths
  typed <- traverse (traverse (\(i, p) -> (,p) <$> IM.lookup i inputs)) fibres
  fromOrderedPaths typed
  where
    inputs = IM.fromDistinctAscList (zip [0 ..] (universe @a))

pathLists :: Bimonoid a b -> OrderedPaths
pathLists arrow = arrow // map (map (B.first (fromIntegral . toNatural))) (V.toList (orderedPaths arrow))

withWidth :: Int -> (forall n. (IsNat n) => Proxy n -> r) -> r
withWidth 0 k = k (Proxy @Nat0)
withWidth n k = withWidth (n - 1) \(_ :: Proxy m) -> k (Proxy @(S m))

readPaths :: Diagram -> Maybe OrderedPaths
readPaths d = do
  inputs <- mergeLeaves (dual d)
  outputs <- mergeLeaves d
  let sources = IM.fromList [(leaf, (input, position)) | (input, leaves) <- zip [0 ..] inputs, (position, leaf) <- zip [0 ..] leaves]
  guard (IM.keys sources == sort (concat outputs))
  traverse (traverse (`IM.lookup` sources)) outputs

-- The two traversals meet on the wires between the copy and merge trees.
mergeLeaves :: Diagram -> Maybe [[Int]]
mergeLeaves (Diagram ins outs boxes) = traverse leaves outs
  where
    inputs = IM.fromList [(input, ()) | input <- ins]
    producers = IM.fromList [(output, box) | box <- boxes, output <- HG.outputs box]
    leaves node = case IM.lookup node producers of
      Just (HG.Box Multiply [l, r] _) -> (++) <$> leaves l <*> leaves r
      Just (HG.Box Unit [] _) -> Just []
      Just (HG.Box Comultiply [_] _) -> Just [node]
      Nothing | IM.member node inputs -> Just [node]
      _ -> Nothing

fromPaths :: Int -> OrderedPaths -> Maybe Diagram
fromPaths inputCount paths = do
  let (firstFresh, outputLeaves) = mapAccumL (\next ps -> (next + length ps, zip ps [next ..])) 0 paths
      byInput = IM.fromListWith (++) [(input, [(position, leaf)]) | ((input, position), leaf) <- concat outputLeaves]
  guard (all (\i -> i >= 0 && i < inputCount) (IM.keys byInput))
  inputLeaves <- traverse (\i -> orderedLeaves (IM.findWithDefault [] i byInput)) [0 .. inputCount - 1]
  let (next, (ins, copies)) = mergeForest firstFresh inputLeaves
      (_, (outs, merges)) = mergeForest next (map (map snd) outputLeaves)
  pure (Diagram ins outs (map dualBox copies ++ merges))
  where
    orderedLeaves leaves = do
      let ordered = sort leaves
      guard (map fst ordered == [0 .. length ordered - 1])
      pure (map snd ordered)

-- Each boundary tree follows the right-associated orientation of the rules.
mergeForest :: Int -> [[Int]] -> (Int, ([Int], [HG.Box Generator Int]))
mergeForest firstFresh fibres =
  let (next, trees) = mapAccumL mergeTree firstFresh fibres
  in (next, (map fst trees, concatMap snd trees))
  where
    mergeTree next [] = (next + 1, (next, [HG.Box Unit [] [next]]))
    mergeTree next [leaf] = (next, (leaf, []))
    mergeTree next (l : rest) =
      let (root, (r, boxes)) = mergeTree next rest
      in (root + 1, (root, HG.Box Multiply [l, r] [root] : boxes))

checkPathRoundTrip :: forall as bs. String -> Graph as bs -> Property ()
checkPathRoundTrip label normal =
  normal // do
    let parts@(Diagram ins _ _) = diagramParts normal
    paths <- maybe (testFailed (label ++ " has no ordered paths")) pure (readPaths parts)
    rebuilt <- maybe (testFailed (label ++ " has invalid path positions")) pure (fromPaths (length ins) paths)
    check (label ++ " changed after reconstruction") (HG.isomorphic normal (diagram @as @bs rebuilt))

checkWordReadback :: Completion.ConvexRules () Generator -> Property ()
checkWordReadback compiled = do
  -- From (x, y, z), discard z, then build (xy, xyx, ε).
  let copyProduct = (comultiply ** wire) . (multiply ** wire) . (wire ** crossing) . (comultiply ** wire)
      host = (wire ** multiply ** unit) . copyProduct . (wire ** wire ** counit)
      examples =
        [ ("original port order", host, [[0, 1], [0, 1, 0], []])
        , ("swapped first two ports", host . (crossing ** wire), [[1, 0], [1, 0, 1], []])
        ]
  expect "word readback needs copying before merging" Nothing (readWords (diagramParts host))
  forM_ examples \(label, forward, wordsInInputs) -> do
    normal <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled forward)
    checkPathRoundTrip ("forward normal form, " ++ label) (R.normalisedGraph normal)
    expect ("forward readback, " ++ label) (Just wordsInInputs) (readWords (diagramParts (R.normalisedGraph normal)))
    -- Reversing the diagram makes the same crossing a swap of output ports.
    let backward = diagram @W3 @W3 (dual (diagramParts forward))
    normalDual <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled backward)
    checkPathRoundTrip ("dual normal form, " ++ label) (R.normalisedGraph normalDual)
    expect
      ("dual readback, " ++ label)
      (Just wordsInInputs)
      (readWords (dual (diagramParts (R.normalisedGraph normalDual))))

checkPathReadback :: Completion.ConvexRules () Generator -> Property ()
checkPathReadback compiled = do
  let examples =
        [ ("straight", multiply . comultiply, [(0, 0), (0, 1)])
        , ("crossed", multiply . crossing . comultiply, [(0, 1), (0, 0)])
        ]
  forM_ examples \(label, host, paths) -> do
    normal <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled host)
    checkPathRoundTrip label (R.normalisedGraph normal)
    let parts = diagramParts (R.normalisedGraph normal)
    expect (label ++ " paths") (Just [paths]) (readPaths parts)
    expect (label ++ " forward word") (Just [[0, 0]]) (readWords parts)
    expect (label ++ " dual word") (Just [[0, 0]]) (readWords (dual parts))

smallPaths :: [i] -> Int -> [[[(i, Int)]]]
smallPaths inputs outputs =
  [ splitOutputs sizes order
  | count <- [0 .. 2]
  , copies <- partitions (length inputs) count
  , sizes <- partitions outputs count
  , order <- permutations [(i, p) | (i, leaves) <- zip inputs copies, p <- [0 .. leaves - 1]]
  ]
  where
    partitions 0 count = [[] | count == 0]
    partitions ports count = [n : rest | n <- [0 .. count], rest <- partitions (ports - 1) (count - n)]
    splitOutputs [] _ = []
    splitOutputs (n : ns) paths = let (out, rest) = splitAt n paths in out : splitOutputs ns rest

checkPathComposition :: Completion.ConvexRules () Generator -> Int -> OrderedPaths -> OrderedPaths -> Property ()
checkPathComposition compiled inputs upstream downstream = do
  first <- maybe (testFailed "invalid upstream paths") pure (fromPaths inputs upstream)
  second <- maybe (testFailed "invalid downstream paths") pure (fromPaths (length upstream) downstream)
  let composite = withWidth inputs \(_ :: Proxy a) ->
        withWidth (length upstream) \(_ :: Proxy b) ->
          withWidth (length downstream) \(_ :: Proxy c) ->
            (\f g -> pathLists (g . f)) <$> pathsFromLists @a @b upstream <*> pathsFromLists @b @c downstream
  expected <- maybe (testFailed "the ordered paths do not compose") pure composite
  HG.reifySorts (wireSorts inputs) \ @as ->
    HG.reifySorts (wireSorts (length upstream)) \ @bs ->
      HG.reifySorts (wireSorts (length downstream)) \ @cs -> do
        let host = diagram @bs @cs second . diagram @as @bs first
        normal <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled host)
        expect
          ("ordered paths for the composite of " ++ show (upstream, downstream) ++ " on " ++ show inputs ++ " inputs")
          (Just expected)
          (readPaths (diagramParts (R.normalisedGraph normal)))

checkPathTensor :: (Int, OrderedPaths) -> (Int, OrderedPaths) -> Property ()
checkPathTensor (leftInputs, left) (rightInputs, right) = do
  l <- maybe (testFailed "invalid left paths") pure (fromPaths leftInputs left)
  r <- maybe (testFailed "invalid right paths") pure (fromPaths rightInputs right)
  let tensor = withWidth leftInputs \(_ :: Proxy a) ->
        withWidth (length left) \(_ :: Proxy b) ->
          withWidth rightInputs \(_ :: Proxy c) ->
            withWidth (length right) \(_ :: Proxy d) ->
              (\f g -> pathLists (f ** g)) <$> pathsFromLists @a @b left <*> pathsFromLists @c @d right
  expected <- maybe (testFailed "invalid tensor factors") pure tensor
  HG.reifySorts (wireSorts leftInputs) \ @as ->
    HG.reifySorts (wireSorts (length left)) \ @bs ->
      HG.reifySorts (wireSorts rightInputs) \ @cs ->
        HG.reifySorts (wireSorts (length right)) \ @ds ->
          expect
            ("ordered paths for the tensor of " ++ show ((leftInputs, left), (rightInputs, right)))
            (Just expected)
            (readPaths (diagramParts (diagram @as @bs l ** diagram @cs @ds r)))

genDiagram :: Property Diagram
genDiagram = do
  width <- Falsify.gen (Gen.elem (2 :| [3, 4]))
  steps <- Falsify.gen (Gen.elem (6 :| [7 .. 10 :: Int]))
  let boundary = [0 .. width - 1]
  start <- permuteOutputs (Diagram boundary boundary [])
  -- A merge followed by a copy guarantees a redex in every sample.
  let seed = addBox (Comultiply, 1, 2) (addBox (Multiply, 2, 1) start)
  foldM (\d _ -> extend d) seed [1 .. steps] >>= permuteOutputs
  where
    permuteOutputs (Diagram ins outs boxes) = do
      order <- Falsify.gen (Gen.elem (outs :| drop 1 (permutations outs)))
      pure (Diagram ins order boxes)
    extend d@(Diagram _ outs _) = do
      op <- Falsify.gen (Gen.elem (operations (length outs)))
      addBox op <$> permuteOutputs d
    operations width
      | width == 5 = (Counit, 1, 0) :| [(Multiply, 2, 1)]
      | otherwise =
          (Unit, 0, 1)
            :| ([(g, 1, n) | width >= 1, (g, n) <- [(Comultiply, 2), (Counit, 0)]] ++ [(Multiply, 2, 1) | width >= 2])
    addBox (label, inputs, outputs) d@(Diagram ins live boxes) =
      let (used, rest) = splitAt inputs live
          fresh = take outputs [nodeCount d ..]
      in Diagram ins (fresh ++ rest) (HG.Box label used fresh : boxes)

checkGeneratedDiagram :: Completion.ConvexRules () Generator -> Diagram -> Property ()
checkGeneratedDiagram compiled d@(Diagram ins outs _) = do
  expected <- HG.reifySorts (replicate (length ins) wireSort) \ @as ->
    HG.reifySorts (replicate (length outs) wireSort) \ @bs -> do
      interpreted <- either testFailed pure (interpretDiagram @as @bs d)
      case interpreted of { Str arrow -> pure (pathLists arrow) }
  HG.reifySorts (wireSorts (length ins)) \ @as ->
    HG.reifySorts (wireSorts (length outs)) \ @bs -> do
      normal <-
        either testFailed pure (Completion.normaliseConvex (R.RewriteLimits (Just 512) Nothing) compiled (diagram @as @bs d))
      check "normalisation reached a normal form" (R.normalisationStatus normal == R.NormalForm)
      check "the diagram needed rewriting" (R.normalisationRewrites normal > 0)
      expect "ordered paths of the normal form" (Just expected) (readPaths (diagramParts (R.normalisedGraph normal)))

test :: TestTree
test =
  testGroup
    "Noncommutative bimonoid"
    [ testGroup
        "Ordered path category"
        [ testCategory @BIPATHS
        , testMonoidal_ @BIPATHS
        , testSymMonoidal_ @BIPATHS
        , testDagger @BIPATHS
        , testInitialObject @BIPATHS
        , testTerminalObject @BIPATHS
        , testMonoid_ @(BP Nat2)
        , testComonoid_ @(BP Nat2)
        , testProperty "the checked constructor requires consecutive distinct copy positions" $ do
            let fibres p q = [(fin0 :: Fin Nat1, p), (fin0, q)] V.::: V.VNil
            expect "duplicate positions" Nothing (fromOrderedPaths (fibres 0 0))
            expect "gap in positions" Nothing (fromOrderedPaths (fibres 0 2))
            expect "negative position" Nothing (fromOrderedPaths (fibres (-1) 0))
            expect "positions in reverse merge order" (Just (fibres 1 0)) (orderedPaths <$> fromOrderedPaths (fibres 1 0))
        , testProperty "the generating wire's comultiplication distinguishes its outputs" $
            check "swapping the two outputs changes comultiplication" $
              Mon.comult @Wire /= swap @BIPATHS @Wire @Wire . Mon.comult @Wire
        ]
    , testProperty "all ten rewrite equations hold for typed ordered-path arrows" $
        forM_ equations \(name, equation) -> withSides equation (checkEquationSemantics name)
    , testProperty "direct evaluation agrees with normalising generated diagrams" $ do
        compiled <- compiledRules
        genDiagram >>= checkGeneratedDiagram compiled
    , testProperty "the 22 noncommutative bimonoid overlaps are joinable" $ do
        namedRules <- either testFailed pure rules
        compiled <- either testFailed pure (Completion.compileConvexRules (map snd namedRules))
        peaks <- either testFailed pure (Completion.criticalOverlaps namedRules)
        expect "number of overlaps" 22 (length peaks)
        forM_ peaks \(Completion.CriticalOverlap first second _ l r) -> do
          left <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled l)
          right <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled r)
          check ("cannot join " ++ show (first, second)) $
            HG.isomorphic (R.normalisedGraph left) (R.normalisedGraph right)
          let label = show (first, second)
          checkPathRoundTrip ("left normal form of " ++ label) (R.normalisedGraph left)
          checkPathRoundTrip ("right normal form of " ++ label) (R.normalisedGraph right)
    , testProperty "different diagrams for the same arrow have isomorphic convex normal forms" $ do
        compiled <- compiledRules
        let left = expandedInteractionLeft
            right = interactionRight
        check "the original diagrams differ" (not (HG.isomorphic left right))
        l <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled left)
        r <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled right)
        check "reduction took several steps" (R.normalisationRewrites l > 1)
        check "normal forms differ" (HG.isomorphic (R.normalisedGraph l) (R.normalisedGraph r))
    , testProperty "forward and dual word readback preserve port order" $
        compiledRules >>= checkWordReadback
    , testProperty "ordered paths distinguish straight wires from crossed wires" $
        compiledRules >>= checkPathReadback
    , testProperty "composing ordered paths agrees with normalising the composite graph" $ do
        compiled <- compiledRules
        let widths = [0 .. 2]
        forM_ [(a, b, c) | a <- widths, b <- widths, c <- widths] \(a, b, c) ->
          forM_
            [(f, g) | f <- smallPaths [0 .. a - 1] b, g <- smallPaths [0 .. b - 1] c]
            (uncurry (checkPathComposition compiled a))
        checkPathComposition compiled 2 [[(0, 2), (1, 0), (0, 0)], [(0, 1)]] [[(0, 1), (0, 0)]]
    , testProperty "tensoring ordered paths agrees with tensoring the graphs" $ do
        let arrows = [(inputs, paths) | inputs <- [0 .. 2], outputs <- [0 .. 2], paths <- smallPaths [0 .. inputs - 1] outputs]
        forM_ arrows \left -> forM_ arrows (checkPathTensor left)
    , testProperty "completion recovers the interaction and right counit rules" $ do
        original <- either testFailed pure rules
        alternative <- either testFailed pure alternativeRules
        let seeds = map snd alternative
        pending <- either testFailed pure (Completion.completeConvex 0 10 compareReducts seeds)
        () <- case pending of
          Completion.ConvexIncomplete _ (Completion.ConvexRuleLimit (Completion.CriticalOverlap 0 1 _ _ _)) -> pure ()
          _ -> testFailed "expected the right unit and expanded interaction to overlap"
        partial <- either testFailed pure (Completion.completeConvex 1 10 compareReducts seeds)
        () <- case partial of
          Completion.ConvexIncomplete retained (Completion.ConvexRuleLimit _) ->
            expect "one learned rule" (length seeds + 1) (length retained)
          _ -> testFailed "expected another unjoinable overlap after learning one rule"
        result <- either testFailed pure (Completion.completeConvex 2 10 compareReducts seeds)
        case result of
          Completion.ConvexComplete final compiled -> do
            expect "number of rules after removing both expansions" 10 (length final)
            recovered <- traverse (recoverRule final) [interaction, rightCounit]
            peaks <- either testFailed pure (Completion.criticalOverlaps recovered)
            check "the learned rules share a critical overlap" $
              any (\(Completion.CriticalOverlap first second _ _ _) -> first /= second) peaks
            forM_ peaks \(Completion.CriticalOverlap first second _ l r) -> do
              left <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled l)
              right <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled r)
              check ("learned rules do not rejoin at " ++ show (first, second)) $
                HG.isomorphic (R.normalisedGraph left) (R.normalisedGraph right)
            reference <- either testFailed pure (Completion.compileConvexRules (map snd original))
            forM_ alternative \(name, seed) -> checkEquation name reference seed
            forM_ (zip [1 :: Int ..] final) \(i, candidate) -> do
              let label = "completed rule " ++ show i
              join $ either testFailed pure $ Completion.withFixedRule candidate \lhs rhs -> do
                let Diagram _ _ boxes = diagramParts lhs
                expect (label ++ " left side has two boxes") 2 (length boxes)
                checkEquationSemantics label lhs rhs
              checkEquation label reference candidate
            forM_ original \(name, originalRule) -> checkEquation name compiled originalRule
          _ -> testFailed "expected completion with two learned rules"
    ]

recoverRule :: [R.Rule () Generator] -> NamedEquation -> Property (String, R.Rule () Generator)
recoverRule final (name, equation) = do
  let matches = withSides equation \lhs rhs ->
        lhs // filter (any (HG.isomorphic rhs) . (`R.rewrites` lhs)) final
  case matches of
    [recovered] -> pure (name, recovered)
    _ -> testFailed ("expected exactly one rule for " ++ name)

compareReducts :: (a :: HG.OPENHG () Generator) ~> b -> a ~> b -> Ordering
compareReducts l r = compare (measure l) (measure r)
  where
    measure g =
      let (_, _, _, boxes) = HG.hypergraphParts g
          interactions =
            length
              [ ()
              | HG.Box Multiply _ [output] <- boxes
              , HG.Box Comultiply [input] _ <- boxes
              , output == input
              ]
      in (interactions, length boxes)

checkEquation :: String -> Completion.ConvexRules () Generator -> R.Rule () Generator -> Property ()
checkEquation name compiled equation = do
  inspect <- either testFailed pure $ Completion.withFixedRule equation \lhs rhs -> do
    let limits = R.RewriteLimits (Just 64) Nothing
    l <- Completion.normaliseConvex limits compiled lhs
    r <- Completion.normaliseConvex limits compiled rhs
    pure
      ( R.normalisationStatus l == R.NormalForm
          && R.normalisationStatus r == R.NormalForm
          && HG.isomorphic (R.normalisedGraph l) (R.normalisedGraph r)
      )
  result <- either testFailed pure inspect
  check ("the two sides of " ++ name ++ " should have the same normal form") result
