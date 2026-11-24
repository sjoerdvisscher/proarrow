{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Merge-and-unit forests present augmented Simplex with ordered inputs
-- and FinSet with symmetric wiring and commutative multiplication.
module Examples.KnuthBendix.MonoidDiagrams (test) where

import Control.Monad (forM_, guard)
import Data.Fin (toNatural, universe)
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List (mapAccumL, permutations, sort, sortOn)
import Data.Set qualified as S
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3, Nat4, Nat6)
import Data.Vec.Lazy qualified as V
import Examples.KnuthBendix.FinSet qualified as FinSet
import Examples.KnuthBendix.Simplex qualified as Simplex
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (**), (.))

import Proarrow.Category.Instance.FinSet qualified as FS
import Proarrow.Category.Instance.OpenHypergraph (W1, W2)
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Instance.Simplex (IsNat (..), Nat, SNat (..), Simplex (..))
import Proarrow.Category.Monoidal (Monoidal (withOb2), MonoidalProfunctor ((**)), SymMonoidal (swap))
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts ((+++)))
import Proarrow.Core (CategoryOf, Promonad (id, (.)), type (~>))
import Proarrow.Object (SomeOb, SomeOf (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.HypergraphRewrite ((==>))
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion

data Generator = MergeBox | UnitBox
  deriving (Eq)

data Tree = Input | Unit | Merge Tree Tree

type Diagram :: [()] -> [()] -> Type
type Diagram as bs = (HG.Wires as :: HG.OPENHG () Generator) ~> HG.Wires bs

wireSorts :: Int -> [HG.SomeSort ()]
wireSorts n = replicate n (Some @'())

merge :: Diagram W2 W1
merge = HG.box MergeBox

unit :: Diagram '[] W1
unit = HG.box UnitBox

wire :: Diagram W1 W1
wire = id

forestDiagram :: (HG.SortList as, HG.SortList bs) => ([Int] -> [Int]) -> [Tree] -> Diagram as bs
forestDiagram order trees =
  HG.unsafeOpenHypergraph (wireSorts count) (order ins) outs boxes
  where
    (count, forest) = mapAccumL (\next tree -> let (end, i, o, bs) = build next tree in (end, (i, o, bs))) 0 trees
    ins = concat [i | (i, _, _) <- forest]
    outs = [o | (_, o, _) <- forest]
    boxes = concat [bs | (_, _, bs) <- forest]
    build next Input = (next + 1, [next], next, [])
    build next Unit = (next + 1, [], next, [HG.Box UnitBox [] [next]])
    build next (Merge l r) =
      let (afterLeft, li, lo, lb) = build next l
          (root, ri, ro, rb) = build afterLeft r
      in (root + 1, li ++ ri, root, lb ++ rb ++ [HG.Box MergeBox [lo, ro] [root]])

data RuleName = Associate | LeftUnit | RightUnit
  deriving (Eq, Ord, Show)

rules :: Either String [(RuleName, R.Rule () Generator)]
rules = do
  assoc <- merge . (merge ** wire) ==> merge . (wire ** merge)
  leftUnit <- merge . (unit ** wire) ==> wire
  rightUnit <- merge . (wire ** unit) ==> wire
  pure [(Associate, assoc), (LeftUnit, leftUnit), (RightUnit, rightUnit)]

compileForestRules :: Property (Completion.ConvexRules () Generator)
compileForestRules = either testFailed pure (rules >>= Completion.compileConvexRules . map snd)

-- Units decrease the number of boxes. Associativity at fixed size
-- decreases the sum of the sizes of the left subtrees of all merges.
joinable :: R.CompiledRules RuleName () Generator -> Completion.CriticalOverlap RuleName () Generator -> Bool
joinable compiled (Completion.CriticalOverlap _ _ _ l r) =
  or [HG.isomorphic x y | x <- normalForms l, y <- normalForms r]
  where
    normalForms
      :: (HG.Wires as :: HG.OPENHG () Generator) ~> HG.Wires bs
      -> [(HG.Wires as :: HG.OPENHG () Generator) ~> HG.Wires bs]
    normalForms host = case R.rewritesCompiled compiled host of
      [] -> [host]
      steps -> concatMap (normalForms . snd) steps

checkOverlaps :: Property ()
checkOverlaps = do
  namedRules <- either testFailed pure rules
  compiled <- either testFailed pure (R.compileRules namedRules)
  peaks <- either testFailed pure (Completion.criticalOverlaps namedRules)
  expect
    "the critical overlaps"
    [(Associate, Associate), (Associate, LeftUnit), (Associate, RightUnit), (Associate, RightUnit), (LeftUnit, RightUnit)]
    (sort [(first, second) | Completion.CriticalOverlap first second _ _ _ <- peaks])
  forM_ peaks \peak@(Completion.CriticalOverlap first second _ _ _) ->
    check ("cannot join " ++ show (first, second)) (joinable compiled peak)

-- In an ordered normal form each output is a unit, an input, or a
-- right-associated merge of inputs with no units.
normalFibres :: Diagram as bs -> Maybe [[Int]]
normalFibres host = traverse readTree outs
  where
    (_, ins, outs, boxes) = HG.hypergraphParts host
    inputNames = IM.fromList (zip ins [0 ..])
    producers = IM.fromList [(out, b) | b <- boxes, out <- HG.outputs b]
    readTree node = case IM.lookup node producers of
      Nothing -> (: []) <$> IM.lookup node inputNames
      Just (HG.Box UnitBox [] [_]) -> Just []
      Just (HG.Box MergeBox [l, r] [_]) -> do
        first <- IM.lookup l inputNames
        rest@(_ : _) <- readTree r
        pure (first : rest)
      _ -> Nothing

table :: [[Int]] -> [Integer]
table fibres =
  [i | (_, i) <- sort [(input, output) | (output, fibre) <- zip [0 ..] fibres, input <- fibre]]

fibresOf :: Int -> [Integer] -> [[Int]]
fibresOf outputs entries =
  [[input | (input, target) <- zip [0 ..] entries, target == output] | output <- take outputs [0 ..]]

forestForFibres :: (HG.SortList as, HG.SortList bs) => (Int -> Tree) -> [[Int]] -> Diagram as bs
forestForFibres tree fibres = forestDiagram inputOrder (map (tree . length) fibres)
  where
    inputOrder nodes = map snd (sortOn fst (zip (concat fibres) nodes))

leftAssociatedTree :: Int -> Tree
leftAssociatedTree size = foldl' Merge Unit (replicate size Input)

rightAssociatedTree :: Int -> Tree
rightAssociatedTree 0 = Unit
rightAssociatedTree size = foldr Merge Input (replicate (size - 1) Input)

partitions :: Int -> Int -> [[Int]]
partitions 0 inputs = [[] | inputs == 0]
partitions outputs inputs =
  [n : rest | n <- [0 .. inputs], rest <- partitions (outputs - 1) (inputs - n)]

checkHomSet :: Completion.ConvexRules () Generator -> (SomeOb Nat, SomeOb Nat) -> Property ()
checkHomSet compiled (Some @a, Some @b) = do
  let m = length (universe @a)
      n = length (universe @b)
      label = show m ++ " → " ++ show n
  ordered <- HG.reifySorts (wireSorts m) \ @as -> HG.reifySorts (wireSorts n) \ @bs ->
    traverse (readNormal compiled . forestDiagram @as @bs id . map leftAssociatedTree) (partitions n m)
  simplex <- maybe (testFailed "missing Simplex hom-set") pure (Simplex.normalFormTables @a @b)
  expect ("ordered normal forms " ++ label) (sort simplex) (sort (map table ordered))
  finSet <- either testFailed pure (FinSet.normalFormTables @a @b)

  -- Permuting the input boundary only renames leaves. In FinSet the
  -- commutative merge forgets their order within each output fibre.
  let commutative =
        S.fromList
          [ map (sort . map (permutation !!)) fibres
          | fibres <- ordered
          , permutation <- permutations [0 .. m - 1]
          ]
  expect ("commutative normal forms " ++ label) (sort finSet) (sort (map table (S.toList commutative)))

checkComposition :: Completion.ConvexRules () Generator -> (SomeOb Nat, SomeOb Nat, SomeOb Nat) -> Property ()
checkComposition compiled (Some @a, Some @b, Some @c) = do
  simplexF <- maybe (testFailed "missing Simplex hom-set") pure (Simplex.normalFormMaps @a @b)
  simplexG <- maybe (testFailed "missing Simplex hom-set") pure (Simplex.normalFormMaps @b @c)
  finSetF <- either testFailed pure (FinSet.normalFormMaps @a @b)
  finSetG <- either testFailed pure (FinSet.normalFormMaps @b @c)
  HG.reifySorts (wireSorts m) \ @as -> HG.reifySorts (wireSorts n) \ @bs -> HG.reifySorts (wireSorts p) \ @cs -> do
    forM_
      (composites Simplex.images Simplex.images Simplex.images simplexF simplexG)
      (checkDiagrams @as @bs @cs "Simplex" id)
    forM_
      (composites FinSet.table FinSet.table FinSet.table finSetF finSetG)
      (checkDiagrams @as @bs @cs "FinSet" (map sort))
  where
    m = length (universe @a)
    n = length (universe @b)
    p = length (universe @c)
    composites
      :: (CategoryOf k)
      => ((x :: k) ~> y -> [Integer])
      -> (y ~> z -> [Integer])
      -> (x ~> z -> [Integer])
      -> [x ~> y]
      -> [y ~> z]
      -> [([Integer], [Integer], [Integer])]
    composites readF readG readComposite fs gs =
      [(readF f, readG g, readComposite (g . f)) | f <- fs, g <- gs]
    checkDiagrams
      :: forall (as :: [()]) (bs :: [()]) (cs :: [()])
       . (HG.SortList as, HG.SortList bs, HG.SortList cs)
      => String -> ([[Int]] -> [[Int]]) -> ([Integer], [Integer], [Integer]) -> Property ()
    checkDiagrams category canonical (f, g, gf) = do
      let input = forestForFibres @as @bs rightAssociatedTree (fibresOf n f)
          output = forestForFibres @bs @cs rightAssociatedTree (fibresOf p g)
      actual <- readNormal compiled (output . input)
      expect
        (category ++ " composite of " ++ show (f, g) ++ " with " ++ show p ++ " outputs")
        (fibresOf p gf)
        (canonical actual)

checkTensor
  :: Completion.ConvexRules () Generator -> (SomeOb Nat, SomeOb Nat) -> (SomeOb Nat, SomeOb Nat) -> Property ()
checkTensor compiled (Some @a, Some @b) (Some @c, Some @d) = do
  simplexF <- maybe (testFailed "missing Simplex hom-set") pure (Simplex.normalFormMaps @a @b)
  simplexG <- maybe (testFailed "missing Simplex hom-set") pure (Simplex.normalFormMaps @c @d)
  finSetF <- either testFailed pure (FinSet.normalFormMaps @a @b)
  finSetG <- either testFailed pure (FinSet.normalFormMaps @c @d)
  let m = length (universe @b)
      n = length (universe @d)
  HG.reifySorts (wireSorts (length (universe @a))) \ @as -> HG.reifySorts (wireSorts m) \ @bs ->
    HG.reifySorts (wireSorts (length (universe @c))) \ @cs -> HG.reifySorts (wireSorts n) \ @ds -> do
      let checkDiagrams :: String -> ([[Int]] -> [[Int]]) -> [Integer] -> [Integer] -> [Integer] -> Property ()
          checkDiagrams category canonical f g expected = do
            let left = forestForFibres @as @bs leftAssociatedTree (fibresOf m f)
                right = forestForFibres @cs @ds leftAssociatedTree (fibresOf n g)
            actual <- readNormal compiled (left ** right)
            expect
              (category ++ " tensor of " ++ show (f, g) ++ " with output sizes " ++ show (m, n))
              (fibresOf (m + n) expected)
              (canonical actual)
      forM_ [(f, g) | f <- simplexF, g <- simplexG] \(f, g) ->
        checkDiagrams "Simplex" id (Simplex.images f) (Simplex.images g) $
          withOb2 @Nat @a @c (withOb2 @Nat @b @d (Simplex.images (f ** g)))
      forM_ [(f, g) | f <- finSetF, g <- finSetG] \(f, g) ->
        checkDiagrams "FinSet" (map sort) (FinSet.table f) (FinSet.table g) (FinSet.table (f +++ g))

readNormal :: Completion.ConvexRules () Generator -> Diagram as bs -> Property [[Int]]
readNormal compiled host = do
  result <- either testFailed pure (Completion.normaliseConvex R.unlimitedRewrites compiled host)
  maybe (testFailed "expected a right-associated merge forest") pure (normalFibres (R.normalisedGraph result))

readSimplex :: forall a b. (IsNat a, IsNat b) => [[Int]] -> Maybe (Simplex a b)
readSimplex fibres = do
  guard (concat fibres == [0 .. length (universe @a) - 1])
  fromCounts @a @b (map length fibres)
  where
    fromCounts :: forall x y. (IsNat x, IsNat y) => [Int] -> Maybe (Simplex x y)
    fromCounts counts = case (singNat @x, singNat @y, counts) of
      (SZ, SZ, []) -> Just ZZ
      (_, SS @y', 0 : rest) -> Y <$> fromCounts @x @y' rest
      (SS @x', SS, n : rest) -> X <$> fromCounts @x' @y ((n - 1) : rest)
      _ -> Nothing

readFinSet :: forall a b. (IsNat a, IsNat b) => [[Int]] -> Maybe (FS.FinSet (FS.FS a) (FS.FS b))
readFinSet fibres = do
  guard (length fibres == length (universe @b))
  guard (sum (map length fibres) == length (universe @a))
  let images = IM.fromList [(input, output) | (output, fibre) <- zip (universe @b) fibres, input <- fibre]
  FS.FinSet <$> traverse (\i -> IM.lookup (fromIntegral (toNatural i)) images) (V.universe @a)

checkGeneratorDiagram :: Completion.ConvexRules () Generator -> Property ()
checkGeneratorDiagram compiled = do
  let mergeThree = merge . (merge ** (merge . (wire ** unit)))
      ordered = mergeThree ** unit ** mergeThree
      crossing = swap @(HG.OPENHG () Generator) @(HG.Wires W1) @(HG.Wires W1)
      crossed = ordered . ((wire ** wire) ** crossing ** (wire ** wire))
  orderedFibres <- readNormal compiled ordered
  simplex <- maybe (testFailed "expected a Simplex arrow") pure (readSimplex @Nat6 @Nat3 orderedFibres)
  expect "ordered forest" [0, 0, 0, 2, 2, 2] (Simplex.images simplex)
  crossedFibres <- readNormal compiled crossed
  finSet <- maybe (testFailed "expected a FinSet arrow") pure (readFinSet @Nat6 @Nat3 crossedFibres)
  expect "forest with a crossing" [0, 0, 2, 0, 2, 2] (FinSet.table finSet)
  expect "the crossed forest has no ordered readback" Nothing (readSimplex @Nat6 @Nat3 crossedFibres)

test :: TestTree
test =
  testGroup
    "Monoid diagrams"
    [ testProperty "associativity and unit overlaps are joinable" checkOverlaps
    , testProperty "ordered and commutative forests agree with bounded Simplex and FinSet" $ do
        compiled <- compileForestRules
        let sizes = [Some @Nat0, Some @Nat1, Some @Nat2, Some @Nat3, Some @Nat4]
        forM_ [(a, b) | a <- sizes, b <- sizes] (checkHomSet compiled)
        let forest = [Merge Input Input]
            build = forestDiagram @W2 @W1
        left <- readNormal compiled (build id forest)
        right <- readNormal compiled (build reverse forest)
        expect "ordered merges remember swapped inputs" ([[0, 1]], [[1, 0]]) (left, right)
        expect "commutative merges forget the swap" (map sort left) (map sort right)
    , testProperty "forest composition agrees with Simplex and FinSet" $ do
        compiled <- compileForestRules
        let sizes = [Some @Nat0, Some @Nat1, Some @Nat2, Some @Nat3]
        forM_ [(a, b, c) | a <- sizes, b <- sizes, c <- sizes] (checkComposition compiled)
    , testProperty "forest tensor agrees with ordinal sum and disjoint union" $ do
        compiled <- compileForestRules
        let sizes = [Some @Nat0, Some @Nat1, Some @Nat2, Some @Nat3]
            boundaries = [(a, b) | a <- sizes, b <- sizes]
        forM_ boundaries \left -> forM_ boundaries (checkTensor compiled left)
    , testProperty "read concrete arrows from a diagram built from generators" $
        compileForestRules >>= checkGeneratorDiagram
    ]
