-- | The ZX cleanup presentation and its learned Hadamard rules.
module Examples.ZXRewrite.Rules where

import Data.Containers.ListUtils (nubOrd)
import Data.Either (partitionEithers)
import Data.IntMap.Strict qualified as IM
import Data.List (find, partition, sortOn)
import Data.Monoid (Ap (..))
import Numeric.Natural (Natural)
import Prelude

import Examples.ZXRewrite.Diagram
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Tools.HypergraphRewrite qualified as R
import Proarrow.Tools.HypergraphRewrite.Completion qualified as Completion

-- Numbered wires on the boundary survive the rewrite. Repeating a wire on
-- the right merges the corresponding boundary positions.
portDiagram :: [Int] -> [HG.Box l R.Port] -> R.PortGraph () l
portDiagram boundary boxes = R.PortGraph (sorts (1 + maximum wireNumbers)) boundary boxes
  where
    wireNumbers = -1 : boundary ++ [n | box <- boxes, R.Node n <- ports box]

closedPorts :: [HG.Box l R.Port] -> R.PortGraph () l
closedPorts = portDiagram []

infix 1 ==>

(==>)
  :: (Eq a)
  => R.PortGraph () (Generator (R.Parameter a))
  -> R.PortGraph () (Generator (R.Parameter a))
  -> Either String (R.Rule () (Generator a))
(==>) = R.parameterPortRule

spiderWithPorts :: Colour -> a -> [R.Port] -> HG.Box (Generator a) R.Port
spiderWithPorts colour angle = HG.Box (Spider colour angle) []

hadamardPorts :: (Int, Int) -> HG.Box (Generator a) R.Port
hadamardPorts (a, b) = HG.Box Hadamard [] [R.Node a, R.Node b]

wireOrders :: Int -> Int -> [(Int, Int)]
wireOrders a b = [(a, b), (b, a)]

spiderFusionRule :: (Eq a) => (a -> a -> a) -> Colour -> Either String (R.Rule () (Generator a))
spiderFusionRule add colour =
  closedPorts [spiderBox alpha [a, link, b], spiderBox beta [c, link, d]]
    ==> closedPorts [spiderBox (R.zipParameters add alpha beta) [a, b, c, d]]
  where
    spiderBox = spiderWithPorts colour
    alpha = R.Variable "alpha"
    beta = R.Variable "beta"
    a = R.Capture "a"
    b = R.Capture "b"
    c = R.Capture "c"
    d = R.Capture "d"
    link = R.Node 0

spiderLoopRule :: (Eq a) => Colour -> Either String (R.Rule () (Generator a))
spiderLoopRule c =
  closedPorts [spiderBox [leading, link, between, link, trailing]]
    ==> closedPorts [spiderBox [leading, between, trailing]]
  where
    spiderBox = spiderWithPorts c (R.Variable "alpha")
    leading = R.Capture "before"
    between = R.Capture "between"
    trailing = R.Capture "after"
    link = R.Node 0

spiderIdentityRule :: (Eq a) => a -> Colour -> Either String (R.Rule () (Generator a))
spiderIdentityRule zero c =
  portDiagram [0, 1] [spiderWithPorts c (R.Literal zero) [R.Node 0, R.Node 1]]
    ==> portDiagram [0, 0] []

-- The diagonal of H is a pi state scaled by 1/sqrt(2).
-- The single free leg is where completion overlaps the seed with fusion.
zeroPhaseHadamardLoop :: Either String (R.Rule () (Generator PhaseSum))
zeroPhaseHadamardLoop =
  portDiagram [2] [green 0 [R.Node 0, R.Node 1, R.Node 2], hadamardPorts (0, 1)]
    ==> portDiagram [0] [green 1 [R.Node 0], HG.Box (Scalar (-1) 0) [] []]
  where
    green = spiderWithPorts Z . R.Literal . phaseConstant

hadamardSymmetry :: Generator a -> R.PortSymmetry
hadamardSymmetry Hadamard = R.SymmetricOutputs
hadamardSymmetry _ = R.OrderedPorts

hadamardVariants
  :: String -> Either String (R.Rule () (Generator a)) -> Either String [(String, R.Rule () (Generator a))]
hadamardVariants name build = do
  r <- build
  map (name,) <$> R.parameterPortVariants hadamardSymmetry r

colourChangeRule :: (Eq a) => Either String (R.Rule () (Generator a))
colourChangeRule =
  R.parameterPortRuleMap
    (closedPorts [spiderWithPorts X alpha legs])
    [("legs", HG.Box Hadamard [] [R.Outer, R.Inner])]
    (closedPorts [spiderWithPorts Z alpha legs])
  where
    alpha = R.Variable "alpha"
    legs = [R.Capture "legs"]

fixedCleanupRules
  :: (Eq a)
  => Bool
  -> a
  -> (a -> a -> a)
  -> [(String, R.Rule () (Generator a))]
  -> Either String [(String, R.Rule () (Generator a))]
fixedCleanupRules removeIdentities zero add hadamardRules = do
  identities <- traverse sequenceA [("identity", spiderIdentityRule zero colour) | removeIdentities, colour <- [Z, X]]
  spiders <-
    traverse sequenceA $
      [("loop", spiderLoopRule colour) | colour <- [Z, X]]
        ++ [("fusion", spiderFusionRule add colour) | colour <- [Z, X]]
  let (early, contractions) = partition ((`elem` ["Hadamard loop", "parallel Hadamard edges"]) . fst) hadamardRules
  pure (early ++ identities ++ contractions ++ spiders)

-- Two ordinary wires between opposite colours contribute a factor of 1/2.
oppositeColourCancellation :: (Eq a) => [Either String (R.Rule () (Generator a))]
oppositeColourCancellation =
  [ closedPorts
      [ red alpha [a, R.Node 0, b, R.Node 1, c]
      , green beta [d, R.Node first, e, R.Node second, f]
      ]
      ==> closedPorts [red alpha [a, b, c], green beta [d, e, f], HG.Box (Scalar (-2) 0) [] []]
  | (first, second) <- wireOrders 0 1
  ]
  where
    red = spiderWithPorts X
    green = spiderWithPorts Z
    alpha = R.Variable "alpha"
    beta = R.Variable "beta"
    a = R.Capture "a"
    b = R.Capture "b"
    c = R.Capture "c"
    d = R.Capture "d"
    e = R.Capture "e"
    f = R.Capture "f"

data ScalarProduct = ScalarProduct Int Rational
  deriving (Eq)

instance Semigroup ScalarProduct where
  ScalarProduct p a <> ScalarProduct q b = ScalarProduct (p + q) (phase (a + b))

instance Monoid ScalarProduct where
  mempty = ScalarProduct 0 0

-- A nullary green pi spider is exact zero, which absorbs other scalars.
zxScalar :: (Eq a) => a -> a -> Generator a -> Maybe (Ap Maybe ScalarProduct)
zxScalar _ _ (Scalar power angle) = Just (Ap (Just (ScalarProduct power (phase angle))))
zxScalar zero piPhase (Spider Z angle)
  | angle == zero = Just (Ap (Just (ScalarProduct 2 0)))
  | angle == piPhase = Just (Ap Nothing)
zxScalar _ _ _ = Nothing

symbolicScalar :: Generator PhaseSum -> Maybe (Ap Maybe ScalarProduct)
symbolicScalar = zxScalar (phaseConstant 0) (phaseConstant 1)

collectScalarBoxes :: (Eq a) => a -> a -> [HG.Box (Generator a) n] -> [HG.Box (Generator a) n]
collectScalarBoxes zero piPhase boxes = ordinary ++ combined
  where
    classify box@(HG.Box l [] []) = maybe (Right box) Left (zxScalar zero piPhase l)
    classify box = Right box
    (scalars, ordinary) = partitionEithers (map classify boxes)
    combined = case getAp (mconcat scalars) of
      Nothing -> [HG.Box (Spider Z piPhase) [] []]
      Just (ScalarProduct power angle) -> [HG.Box (Scalar power angle) [] [] | power /= 0 || angle /= 0]

-- A formal sum of independent phase variables. Substituting rational phases
-- and reducing modulo two commutes with addition, so equality of sums proves
-- equality for every assignment to the spiders.
data PhaseSum = PhaseSum Rational (IM.IntMap Natural)
  deriving (Eq, Ord, Show)

phaseConstant :: Rational -> PhaseSum
phaseConstant a = PhaseSum a IM.empty

phaseVariable :: Int -> PhaseSum
phaseVariable i = PhaseSum 0 (IM.singleton i 1)

addPhaseSums :: PhaseSum -> PhaseSum -> PhaseSum
addPhaseSums (PhaseSum a as) (PhaseSum b bs) = PhaseSum (phase (a + b)) (IM.unionWith (+) as bs)

phaseParameter :: (Rational -> a) -> (a -> a -> a) -> (Natural -> a -> a) -> PhaseSum -> R.Parameter a
phaseParameter literal add scale (PhaseSum offset coefficients) =
  case constants ++ map term (IM.toAscList coefficients) of
    [] -> R.Literal (literal 0)
    first : rest -> foldl' (R.zipParameters add) first rest
  where
    constants = [R.Literal (literal offset) | offset /= 0]
    term (i, coefficient) =
      let variable = R.Variable ("phase" ++ show i)
      in if coefficient == 1 then variable else R.mapParameter (scale coefficient) variable

symbolicPhaseParameter :: PhaseSum -> R.Parameter PhaseSum
symbolicPhaseParameter = phaseParameter phaseConstant addPhaseSums scale
  where
    scale n (PhaseSum offset coefficients) = PhaseSum (phase (fromIntegral n * offset)) (fmap (n *) coefficients)

rationalPhaseParameter :: PhaseSum -> R.Parameter Rational
rationalPhaseParameter = phaseParameter phase (\a b -> phase (a + b)) (\n a -> phase (fromIntegral n * a))

-- A coefficient-one variable private to a shared expression can be solved
-- for modulo two. All other phases are independent of that choice, so the
-- expression can be bound as one arbitrary phase in the learned rule.
reparameterisePhases :: [PhaseSum] -> [PhaseSum] -> PhaseSum -> PhaseSum
reparameterisePhases left right value = maybe value phaseVariable (lookup value replacements)
  where
    replacements =
      [ (expression, i)
      | expression@(PhaseSum offset terms) <- nubOrd left
      , expression `elem` right
      , offset /= 0 || IM.size terms /= 1
      , Just (i, _) <- [find (private expression) (IM.toList terms)]
      ]
    private expression (i, coefficient) =
      coefficient == 1 && all (\p@(PhaseSum _ terms) -> p == expression || IM.notMember i terms) (left ++ right)

zxPortSymmetry :: Generator a -> Completion.PortSymmetry
zxPortSymmetry Spider{} = Completion.SymmetricPorts
zxPortSymmetry generator = hadamardSymmetry generator

zxCompletionOrder :: R.PortGraph () (Generator a) -> R.PortGraph () (Generator a) -> Ordering
zxCompletionOrder left right = compare (zxCompletionRank left) (zxCompletionRank right)

zxCompletionRank :: R.PortGraph () (Generator a) -> (Int, Int, Int)
zxCompletionRank (R.PortGraph _ _ boxes) =
  (length [() | HG.Box (Spider X _) _ _ <- boxes], length boxes, sum (map (length . ports) boxes))

-- Colour change can add Hadamards, so red spiders come first. The trace is
-- one Hadamard box and its zero-valued reduct has two scalar boxes. Counting
-- Hadamards first orients that rule toward zero. Counting ports before total
-- boxes lets the opposite-colour cancellation add a scalar.
zxHadamardCompletionOrder :: R.PortGraph () (Generator a) -> R.PortGraph () (Generator a) -> Ordering
zxHadamardCompletionOrder left right = compare (rank left) (rank right)
  where
    rank graph@(R.PortGraph _ _ boxes) =
      let (red, count, degree) = zxCompletionRank graph
      in (red, length [() | HG.Box Hadamard _ _ <- boxes], degree, count)

zxPortParameters :: Completion.ParameterPortOptions Generator PhaseSum Rational
zxPortParameters =
  (Completion.parameterPortOptions phaseVariable symbolicPhaseParameter rationalPhaseParameter)
    { Completion.portComparison = Completion.ComparePortScalars zxPortSymmetry symbolicScalar
    }

zxHadamardParameters :: Completion.ParameterPortOptions Generator PhaseSum Rational
zxHadamardParameters =
  zxPortParameters
    { Completion.matchingPortSymmetry = hadamardSymmetry
    , Completion.reparameterise = reparameterisePhases
    }

completedAttachedHadamardLoops
  :: Either String ([R.Rule () (Generator PhaseSum)], [R.Rule () (Generator Rational)])
completedAttachedHadamardLoops = do
  zeroLoop <- zeroPhaseHadamardLoop
  fusion <- spiderFusionRule addPhaseSums Z
  result <-
    Completion.completeParameterPorts
      zxHadamardParameters{Completion.matchingPortSymmetry = zxPortSymmetry}
      (Completion.PortCompletionOptions 1 4 zxHadamardCompletionOrder)
      [zeroLoop, fusion]
  case result of
    (Completion.PortComplete (_ : _ : learned) _, emitted@(_ : _)) -> pure (learned, emitted)
    _ -> Left "ZX cleanup: attached Hadamard-loop completion did not finish"

completeHadamardCleanup
  :: Either String (Completion.PortCompletion (Generator PhaseSum), [R.Rule () (Generator Rational)])
completeHadamardCleanup = do
  (attached, _) <- completedAttachedHadamardLoops
  seeds <-
    sequence
      [spiderIdentityRule (phaseConstant 0) Z, spiderIdentityRule (phaseConstant 0) X, colourChangeRule, spiderLoopRule Z]
  Completion.completeParameterPorts
    zxHadamardParameters
    (Completion.PortCompletionOptions 3 4 zxHadamardCompletionOrder)
    (seeds ++ attached)

completedHadamardRules
  :: Either String ([R.Rule () (Generator PhaseSum)], [R.Rule () (Generator Rational)])
completedHadamardRules = do
  result <- completeHadamardCleanup
  case result of
    (Completion.PortComplete completed _, emitted) ->
      pure (drop (length completed - length emitted) completed, emitted)
    _ -> Left "ZX cleanup: Hadamard completion did not finish"

learnedHadamardRules :: Either String [(String, R.Rule () (Generator Rational))]
learnedHadamardRules = do
  attached <- snd <$> completedAttachedHadamardLoops
  bare <- completedHadamardRules >>= nameHadamardRules 0 1 . snd
  parallel <- snd <$> completedParallelHadamardEdges
  pure (map ("Hadamard loop",) attached ++ bare ++ map ("parallel Hadamard edges",) parallel)

completedParallelHadamardEdges
  :: Either String ([R.Rule () (Generator PhaseSum)], [R.Rule () (Generator Rational)])
completedParallelHadamardEdges = do
  bare <- completedHadamardRules >>= nameHadamardRules (phaseConstant 0) (phaseConstant 1) . fst
  colour <- colourChangeRule
  opposite <- sequence oppositeColourCancellation
  -- Put colour change first so completion sees the two-spider overlap
  -- before the three-spider self-overlaps of opposite-colour cancellation.
  let seeds = colour : opposite ++ [r | ("Hadamard chain", r) <- bare]
  result <-
    Completion.completeParameterPorts
      zxHadamardParameters
      (Completion.PortCompletionOptions 2 4 zxHadamardCompletionOrder)
      seeds
  case result of
    (Completion.PortComplete completed _, emitted@(_ : _)) ->
      pure (drop (length seeds) completed, emitted)
    _ -> Left "ZX cleanup: parallel Hadamard completion did not finish"

nameHadamardRules :: (Eq a) => a -> a -> [R.Rule () (Generator a)] -> Either String [(String, R.Rule () (Generator a))]
nameHadamardRules zero piPhase = fmap (sortOn fst) . traverse name
  where
    name rule = do
      (left@(R.PortGraph _ boundary boxes), R.PortGraph ns interface rhs) <- R.parameterPortExample (const zero) rule
      case (length boundary, map HG.label boxes) of
        (1, [Hadamard, Hadamard]) -> pure ("retain wire", rule)
        (2, [Hadamard, Hadamard]) -> pure ("Hadamard chain", rule)
        (0, [Hadamard]) -> do
          -- This learned rule has no label parameters. Fold its scalar product
          -- before returning it to the matcher.
          compact <- literal left ==> literal (R.PortGraph ns interface (collectScalarBoxes zero piPhase rhs))
          pure ("Hadamard loop", compact)
        _ -> Left "ZX cleanup: unexpected learned Hadamard rule"
    literal (R.PortGraph ns boundary boxes) =
      R.PortGraph ns boundary [HG.Box (fmap R.Literal l) ins outs | HG.Box l ins outs <- boxes]

learnedSymbolicCleanupRules :: Either String [(String, R.Rule () (Generator PhaseSum))]
learnedSymbolicCleanupRules = do
  let zero = phaseConstant 0
      piPhase = phaseConstant 1
  attached <- fst <$> completedAttachedHadamardLoops
  bare <- completedHadamardRules >>= nameHadamardRules zero piPhase . fst
  parallel <- fst <$> completedParallelHadamardEdges
  fixedCleanupRules
    True
    zero
    addPhaseSums
    (map ("Hadamard loop",) attached ++ bare ++ map ("parallel Hadamard edges",) parallel)
