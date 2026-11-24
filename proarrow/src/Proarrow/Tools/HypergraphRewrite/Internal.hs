-- | Shared graph representation, rule construction, and application of matches.
module Proarrow.Tools.HypergraphRewrite.Internal
  ( Graph (..)
  , graph
  , mapLabels
  , traverseLabels
  , sameGraph
  , Rule (..)
  , rule
  , Parameter (Literal, Variable)
  , mapParameter
  , parameterRule
  , subgraphRule
  , withSortParameters
  , Port (..)
  , PortGraph (..)
  , portRule
  , parameterPortRule
  , parameterPortRuleWith
  , rulePattern
  , hasSubgraphs
  , LabelTest (..)
  , sameLabelTest
  , acceptsLabel
  , Match
  , Prepared
  , portsOf
  , internalNodes
  , deletedImages
  , nonConflictingBy
  , matches
  , replaceMany
  , replaceSelected
  , RewriteLimits (..)
  , unlimitedRewrites
  , NormalisationStatus (..)
  , NormalisationResult (..)
  , normaliseBy
  , normaliseGraphBy
  ) where

import Control.Monad (foldM, unless, void, when)
import Data.Either (isRight)
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Type)
import Data.List (genericTake, mapAccumL)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable, eqT)
import Data.Vector qualified as V
import Numeric.Natural (Natural)
import Prelude

import Proarrow.Category.Instance.FinHask (unionFind)
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , OPENHG
  , SomeSort
  , Wires
  , hypergraphParts
  , sameSort
  , unsafeOpenHypergraph
  )
import Proarrow.Core (CategoryOf (..), Kind, (//))
import Proarrow.Optic.Iso (DecidableIso)

type Graph :: Kind -> Type -> Type
data Graph s l = Graph [SomeSort s] [Int] [Int] [Box l Int]

-- | An oriented equation between diagrams with the same input and output sorts.
-- Construct with 'rule', 'parameterRule' or 'subgraphRule'. The interface consists of all boundary positions.
type Rule :: Kind -> Type -> Type
data Rule s l
  = Rule (Graph s (LabelTest l)) ([l] -> Maybe (Graph s l))
  | PortRule (PortGraph s (LabelTest l)) (M.Map String [Int] -> [l] -> Maybe (PortGraph s l))
  | SortRule ([SomeSort s] -> [SomeSort s] -> [SomeSort s] -> Maybe [SomeSort s]) (Rule s l)
  | SubgraphRule (Graph s (Either l String)) (Graph s (Either l String))

-- | Unary arrow parameters with explicit input and output boundaries. The
-- classifier returns 'Left' for a literal label or 'Right' for a parameter name.
-- Parameters capture connected regions with no external connections except their two boundaries;
-- identity captures identify those boundaries. Repeated names require boundary-
-- preserving graph isomorphism. RHS occurrences copy the captured region with
-- fresh internal nodes; omitted parameters are discarded.
--
-- This restricted higher-order matching follows the fixed-interface approach
-- of <https://arxiv.org/abs/1211.4098 Higher-order port-graph rewriting>.
-- Concrete boxes share the discrimination net. Capture regions are recovered
-- from connected components after cutting at the matched pattern nodes.
-- Disconnected captures and non-identity captures with coincident endpoints
-- are not supported. Boundary nodes must each have one incident captured port,
-- an input and an output respectively. Matching is structural, not modulo laws.
-- Each complete match must contain at least one box; an unanchored identity
-- cannot match. Structurally identical replacements are skipped. Identity
-- captures may identify pattern nodes only across that parameter's endpoints.
subgraphRule
  :: (p -> Either l String)
  -> (a :: OPENHG s p) ~> b
  -> a ~> b
  -> Either String (Rule s l)
subgraphRule classify lhs rhs = do
  checkInterface left
  unless (all unary (lb ++ rb)) (Left "subgraphRule: arrow parameters must have one input and one output")
  unless (S.isSubsetOf (names rb) (names lb)) (Left "subgraphRule: unbound arrow parameter on the right")
  pure (SubgraphRule left right)
  where
    left@(Graph _ _ _ lb) = mapLabels classify (graph lhs)
    right@(Graph _ _ _ rb) = mapLabels classify (graph rhs)
    unary (Box (Right _) i o) = length i == 1 && length o == 1
    unary _ = True
    names bs = S.fromList [n | Box (Right n) _ _ <- bs]

-- | Defer a rule's sort checks to a per-match instantiation. The callback receives
-- the numbered pattern sorts, their matched host sorts, and replacement sorts.
-- Return one instantiated sort per replacement node, or reject the candidate.
-- The callback must validate the pattern sorts against the matched host sorts.
-- Interface sorts are checked against the host before a replacement is accepted.
-- Box selection and node binding still share the compiled discrimination net.
withSortParameters
  :: ([SomeSort s] -> [SomeSort s] -> [SomeSort s] -> Maybe [SomeSort s])
  -> Rule s l
  -> Rule s l
withSortParameters = SortRule

-- | A numbered node, a named sequence of ports, or one element of a captured
-- sequence. Captures may be empty and preserve order and repeated nodes.
-- 'Element' is available only on the right of a port rule.
data Port = Node Int | Capture String | Element String Int
  deriving (Eq, Ord, Show)

-- | A port-rule fragment: sorts of numbered nodes, its explicit interface, and
-- boxes. Every captured node is also preserved, including aliases between
-- captures or with explicit interface nodes. RHS numbered nodes are fresh,
-- except where glued to the left through the two explicit interfaces.
type PortGraph :: Kind -> Type -> Type
data PortGraph s l = PortGraph [SomeSort s] [Int] [Box l Port]

mapPortLabels :: (l -> m) -> PortGraph s l -> PortGraph s m
mapPortLabels f (PortGraph ns interface bs) = PortGraph ns interface [Box (f l) i o | Box l i o <- bs]

portLabels :: PortGraph s l -> [l]
portLabels (PortGraph _ _ bs) = map label bs

-- | Match variable port sequences with literal labels. A capture on the left
-- matches a contiguous sequence; use captures before and after a numbered node
-- to find a connection at any port position. Repeated names require equal
-- sequences. Captured nodes cannot be deleted, even when they alias numbered
-- nodes. Existing dangling, sort, injectivity and batch-conflict checks apply.
portRule :: (DecidableIso s) => PortGraph s l -> PortGraph s l -> Either String (Rule s l)
portRule lhs rhs = do
  checkPortLeft lhs
  checkPortRight lhs rhs
  pure (PortRule (mapPortLabels ExactLabel lhs) (\_ _ -> Just rhs))

-- | A port rule with the label parameters of 'parameterRule'. Both its
-- topology template and parameter names are checked when constructing the rule.
parameterPortRule
  :: (DecidableIso s, Traversable f, Eq (f ()), Typeable f, Eq a)
  => PortGraph s (f (Parameter a)) -> PortGraph s (f (Parameter a)) -> Either String (Rule s (f a))
parameterPortRule lhs rhs = do
  checkPortLeft lhs
  checkPortRight lhs rhs
  checkParameters (portLabels lhs) (portLabels rhs)
  parameterPortRuleWith lhs (const rhs)

-- | Build a replacement from capture lengths, for example one Hadamard per
-- captured leg. 'Element' refers to an individual captured port. The builder
-- receives only lengths, not host node IDs. Replacement node references,
-- interface sorts, captures and parameter names are checked for each candidate;
-- an invalid replacement rejects that candidate before batch selection.
parameterPortRuleWith
  :: (DecidableIso s, Traversable f, Eq (f ()), Typeable f, Eq a)
  => PortGraph s (f (Parameter a))
  -> (M.Map String Int -> PortGraph s (f (Parameter a)))
  -> Either String (Rule s (f a))
parameterPortRuleWith lhs build = do
  checkPortLeft lhs
  checkParameters (portLabels lhs) []
  pure (PortRule (mapPortLabels (ConstructorLabel . void) lhs) instantiate)
  where
    instantiate captures labels = do
      let rhs@(PortGraph ns boundary bs) = build (M.map length captures)
      unless (isRight (checkPortRight lhs rhs)) Nothing
      unless (isRight (checkParameters (portLabels lhs) (portLabels rhs))) Nothing
      env <- parameterBindings (portLabels lhs) labels
      boxes <- traverse (\(Box l i o) -> (\l' -> Box l' i o) <$> traverse (`evaluateParameter` env) l) bs
      pure (PortGraph ns boundary boxes)

captureNames :: PortGraph s l -> S.Set String
captureNames (PortGraph _ _ bs) = S.fromList [name | b <- bs, Capture name <- inputs b ++ outputs b]

checkPortNodes :: PortGraph s l -> Either String ()
checkPortNodes (PortGraph ns boundary bs) = do
  let valid n = n >= 0 && n < length ns
  unless
    (all valid boundary && all valid [n | b <- bs, Node n <- inputs b ++ outputs b])
    (Left "portRule: invalid node reference")
  unless
    (all (>= 0) [i | b <- bs, Element _ i <- inputs b ++ outputs b])
    (Left "portRule: negative capture index")

checkPortLeft :: PortGraph s l -> Either String ()
checkPortLeft g@(PortGraph _ boundary bs) = do
  checkPortNodes g
  unless (length boundary == S.size (S.fromList boundary)) (Left "portRule: repeated left interface node")
  when (any element [p | b <- bs, p <- inputs b ++ outputs b]) (Left "portRule: Element on the left")
  where
    element Element{} = True
    element _ = False

checkPortRight :: (DecidableIso s) => PortGraph s l -> PortGraph s m -> Either String ()
checkPortRight lhs@(PortGraph ls li _) rhs@(PortGraph rs ri bs) = do
  checkPortNodes rhs
  unless
    (length li == length ri && and [sameSort (ls !! l) (rs !! r) | (l, r) <- zip li ri])
    (Left "portRule: incompatible explicit interfaces")
  let references =
        S.fromList
          [name | b <- bs, p <- inputs b ++ outputs b, name <- case p of Node _ -> []; Capture n -> [n]; Element n _ -> [n]]
  unless (S.isSubsetOf references (captureNames lhs)) (Left "portRule: unbound port capture")

rulePattern :: Rule s l -> PortGraph s (LabelTest l)
rulePattern (Rule (Graph ns ins outs bs) _) = PortGraph ns (ins ++ outs) (map (fmap Node) bs)
rulePattern (PortRule pattern' _) = pattern'
rulePattern (SortRule _ r) = rulePattern r
rulePattern (SubgraphRule (Graph ns ins outs bs) _) =
  PortGraph ns (ins ++ outs) [fmap Node (Box (ExactLabel l) i o) | Box (Left l) i o <- bs]

hasSubgraphs :: Rule s l -> Bool
hasSubgraphs (SubgraphRule (Graph _ _ _ bs) _) = any (isRight . label) bs
hasSubgraphs (SortRule _ r) = hasSubgraphs r
hasSubgraphs _ = False

-- | A literal value, a named parameter, or a computed replacement value.
-- Repeated names in a rule bind equal values. Arithmetic constructs replacement
-- expressions; computed expressions are rejected on the left of a rule.
type Parameter :: Type -> Type
data Parameter a
  = Literal a
  | Variable String
  | Computed (S.Set String) (M.Map String a -> Maybe a)

-- | Transform a replacement expression, for example to normalise a phase.
mapParameter :: (a -> a) -> Parameter a -> Parameter a
mapParameter f (Literal a) = Literal (f a)
mapParameter f p = Computed (parameterNames p) (fmap f . evaluateParameter p)

zipParameters :: (a -> a -> a) -> Parameter a -> Parameter a -> Parameter a
zipParameters f (Literal a) (Literal b) = Literal (f a b)
zipParameters f a b = Computed (S.union (parameterNames a) (parameterNames b)) \env ->
  f <$> evaluateParameter a env <*> evaluateParameter b env

instance (Num a) => Num (Parameter a) where
  (+) = zipParameters (+)
  (-) = zipParameters (-)
  (*) = zipParameters (*)
  negate = mapParameter negate
  abs = mapParameter abs
  signum = mapParameter signum
  fromInteger = Literal . fromInteger

instance (Fractional a) => Fractional (Parameter a) where
  (/) = zipParameters (/)
  recip = mapParameter recip
  fromRational = Literal . fromRational

parameterNames :: Parameter a -> S.Set String
parameterNames (Literal _) = S.empty
parameterNames (Variable name) = S.singleton name
parameterNames (Computed names _) = names

evaluateParameter :: Parameter a -> M.Map String a -> Maybe a
evaluateParameter (Literal a) _ = Just a
evaluateParameter (Variable name) env = M.lookup name env
evaluateParameter (Computed _ expression) env = expression env

-- The constructor key erases only Traversable fields. All other label data,
-- such as a spider's colour, remains part of discrimination-net dispatch.
type LabelTest :: Type -> Type
data LabelTest l where
  ExactLabel :: l -> LabelTest l
  ConstructorLabel :: (Functor f, Eq (f ()), Typeable f) => f () -> LabelTest (f a)

sameLabelTest :: (Eq l) => LabelTest l -> LabelTest l -> Bool
sameLabelTest (ExactLabel a) (ExactLabel b) = a == b
sameLabelTest (ConstructorLabel (a :: f ())) (ConstructorLabel (b :: g ())) =
  case eqT @f @g of
    Just Refl -> a == b
    Nothing -> False
sameLabelTest _ _ = False

acceptsLabel :: (Eq l) => LabelTest l -> l -> Bool
acceptsLabel (ExactLabel expected) actual = expected == actual
acceptsLabel (ConstructorLabel expected) actual = expected == void actual

-- | Construct a rule. Rejects repeated nodes across the left input and output
-- boundaries, since this implementation requires an injective left interface.
-- For example, a chain of two unary boxes can rewrite to an identity wire;
-- the reverse orientation needs a more general complement construction.
rule :: (a :: OPENHG s l) ~> b -> a ~> b -> Either String (Rule s l)
rule lhs rhs = do
  checkInterface (graph lhs)
  pure (Rule (mapLabels ExactLabel (graph lhs)) (const (Just (graph rhs))))

-- | Construct a rule with parameters in the 'Traversable' fields of its labels.
-- Both diagrams have labels @f (Parameter a)@; hosts have labels @f a@.
-- Constructors and fields outside the traversal match literally. 'Literal'
-- matches one value; 'Variable' binds a name shared across the whole rule.
-- Right-side expressions can use arithmetic and 'mapParameter'. Unbound names
-- and computed left-side expressions are rejected when constructing the rule.
--
-- Rule topology and arity remain fixed. The compiled matcher dispatches on the
-- label with its traversed fields erased, then checks bindings before choosing
-- a batch. Each occurrence gets its own bindings and instantiated replacement.
parameterRule
  :: (Traversable f, Eq (f ()), Typeable f, Eq a)
  => (x :: OPENHG s (f (Parameter a))) ~> y
  -> x ~> y
  -> Either String (Rule s (f a))
parameterRule lhs rhs = do
  checkInterface left
  checkParameters leftLabels (map label rightBoxes)
  pure (Rule (mapLabels (ConstructorLabel . void) left) instantiate)
  where
    left = graph lhs
    right = graph rhs
    Graph _ _ _ leftBoxes = left
    Graph _ _ _ rightBoxes = right
    leftLabels = map label leftBoxes
    instantiate labels = do
      env <- parameterBindings leftLabels labels
      traverseLabels (traverse (`evaluateParameter` env)) right

checkParameters :: (Foldable f) => [f (Parameter a)] -> [f (Parameter a)] -> Either String ()
checkParameters lhs rhs = do
  let left = concatMap toList lhs
      leftNames = S.unions (map parameterNames left)
      rightNames = S.unions (map parameterNames (concatMap toList rhs))
  when (any computed left) (Left "parameterRule: computed expression on the left")
  unless (S.isSubsetOf rightNames leftNames) (Left "parameterRule: unbound parameter on the right")
  where
    computed Computed{} = True
    computed _ = False

parameterBindings :: (Foldable f, Eq a) => [f (Parameter a)] -> [f a] -> Maybe (M.Map String a)
parameterBindings patterns labels = do
  let parameters = concatMap toList patterns
      values = concatMap toList labels
  unless (length parameters == length values) Nothing
  foldM bind M.empty (zip parameters values)
  where
    bind env (Literal expected, actual) = if expected == actual then Just env else Nothing
    bind env (Variable name, actual) = case M.lookup name env of
      Just expected -> if expected == actual then Just env else Nothing
      Nothing -> Just (M.insert name actual env)
    bind _ (Computed{}, _) = Nothing

checkInterface :: Graph s l -> Either String ()
checkInterface (Graph _ ins outs _) =
  let boundary = ins ++ outs
  in if S.size (S.fromList boundary) == length boundary
       then Right ()
       else Left "rule: the left boundary must attach to distinct nodes"

mapLabels :: (l -> m) -> Graph s l -> Graph s m
mapLabels f (Graph ns ins outs bs) = Graph ns ins outs [Box (f l) i o | Box l i o <- bs]

traverseLabels :: (l -> Maybe m) -> Graph s l -> Maybe (Graph s m)
traverseLabels f (Graph ns ins outs bs) = Graph ns ins outs <$> traverse (\(Box l i o) -> (\l' -> Box l' i o) <$> f l) bs

sameGraph :: (Eq l, DecidableIso s) => Graph s l -> Graph s l -> Bool
sameGraph lhs@(Graph ls li lo lb) rhs@(Graph rs ri ro rb) =
  length ls == length rs
    && length lb == length rb
    && any (\((m, _), _) -> map (m IM.!) li == ri && map (m IM.!) lo == ro) (matches (mapLabels ExactLabel lhs) rhs)

graph :: (a :: OPENHG s l) ~> b -> Graph s l
graph h = let (ns, i, o, bs) = hypergraphParts h in Graph ns i o bs

-- Node images and the set of selected host box occurrences.
type Match = (IM.IntMap Int, IS.IntSet)

internalNodes :: Graph s l -> [Int]
internalNodes (Graph ns ins outs _) = [n | n <- [0 .. length ns - 1], IS.notMember n interface]
  where
    interface = IS.fromList (ins ++ outs)

deletedImages :: Graph s l -> IM.IntMap Int -> IS.IntSet
deletedImages lhs m = IS.fromList [m IM.! n | n <- internalNodes lhs]

-- Track both read and deleted nodes: disjoint box sets alone do not protect
-- isolated nodes or interface nodes of another match.
nonConflictingBy :: (a -> Match -> IS.IntSet) -> [(a, Match)] -> [(a, Match)]
nonConflictingBy deletions candidates = reverse chosen
  where
    (chosen, _, _, _) = foldl' select ([], IS.empty, IS.empty, IS.empty) candidates
    select state@(accepted, boxes, nodes, deleted) candidate@(key, match@(mapping, used)) =
      let readNodes = IS.fromList (IM.elems mapping)
          deleteNodes = deletions key match
      in if IS.disjoint boxes used && IS.disjoint deleted readNodes && IS.disjoint nodes deleteNodes
           then (candidate : accepted, IS.union boxes used, IS.union nodes readNodes, IS.union deleted deleteNodes)
           else state

matches :: (Eq l, DecidableIso s) => Graph s (LabelTest l) -> Graph s l -> [(Match, [l])]
matches (Graph ns li lo boxes) (Graph hs hi ho hostBoxes) = do
  (nodes, used, labels) <- matchBoxes plans (IM.empty, IS.empty) IS.empty
  match <- complete [0 .. V.length patternSorts - 1] nodes used
  pure (match, labels)
  where
    patternSorts = V.fromList ns
    hostSorts = V.fromList hs
    host = V.fromList hostBoxes
    numbered = zip [0 ..] hostBoxes
    -- Keep host box order within each node's incidences.
    byNode =
      V.map reverse $
        V.accum
          (flip (:))
          (V.replicate (V.length hostSorts) [])
          [(n, (p, i)) | (i, b) <- numbered, (p, n) <- portsOf b]
    atNode n = byNode V.! n
    boundary = IS.fromList (hi ++ ho)
    interface = IS.fromList (li ++ lo)
    internal = [n | n <- [0 .. V.length patternSorts - 1], IS.notMember n interface]
    plans =
      [ (b, [(i, h) | (i, h) <- numbered, compatible b h])
      | b <- boxes
      ]
    compatible (Box l i o) (Box l' i' o') = acceptsLabel l l' && length i == length i' && length o == length o'
    extend state@(m, range) (x, y)
      | Just y' <- IM.lookup x m = if y == y' then Just state else Nothing
      | IS.member y range = Nothing
      | not (sameSort (patternSorts V.! x) (hostSorts V.! y)) = Nothing
      | otherwise = Just (IM.insert x y m, IS.insert y range)
    matchBoxes [] m used = [(m, used, [])]
    matchBoxes ((b@(Box _ ins outs), base) : rest) nodes@(m, _) used = do
      let constrained =
            [ [i | (s, i) <- atNode y, s == p]
            | (p, x) <- portsOf b
            , Just y <- [IM.lookup x m]
            ]
          candidates = case constrained of
            [] -> [(i, h) | (i, h) <- base, IS.notMember i used]
            first : more ->
              -- Start from the smallest known-port neighbourhood; extend checks every port.
              [ (i, h)
              | i <- foldl' shorter first more
              , IS.notMember i used
              , let h = host V.! i
              , compatible b h
              ]
      (i, Box l ins' outs') <- candidates
      case foldM extend nodes (zip ins ins' ++ zip outs outs') of
        Nothing -> []
        Just nodes' -> [(m', used', l : labels) | (m', used', labels) <- matchBoxes rest nodes' (IS.insert i used)]
    shorter a b = if length a <= length b then a else b
    complete [] (m, _) used
      | all (deletable m used) internal = [(m, used)]
      | otherwise = []
    complete (x : xs) nodes@(m, _) used
      | IM.member x m = complete xs nodes used
      | otherwise = do
          y <- [0 .. V.length hostSorts - 1]
          nodes' <- maybe [] pure (extend nodes (x, y))
          complete xs nodes' used
    deletable m used x =
      let y = m IM.! x
      in IS.notMember y boundary && all (\(_, i) -> IS.member i used) (atNode y)

-- Matches satisfy the dangling condition and have non-conflicting deletions.
replaceMany :: Graph s p -> Graph s l -> Graph s l -> [Match] -> Graph s l
replaceMany lhs rhs host chosen = replaceSelected host [(lhs, rhs, m) | m <- chosen]

replaceSelected :: Graph s l -> [(Graph s p, Graph s l, Match)] -> Graph s l
replaceSelected (Graph hs hi ho hb) chosen =
  Graph (IM.elems nodeSorts) (map renumber hi) (map renumber ho) (map (fmap renumber) boxes)
  where
    deleted = IS.unions [deletedImages lhs mapping | (lhs, _, (mapping, _)) <- chosen]
    selected = IS.unions [used | (_, _, (_, used)) <- chosen]
    retainedBoxes = [b | (i, b) <- zip [0 ..] hb, IS.notMember i selected]
    (_, copies) = mapAccumL (\start entry@(_, Graph rs _ _ _, _) -> (start + length rs, (start, entry))) (length hs) chosen
    root =
      unionFind
        [ (mapping IM.! l, start + r)
        | (start, (Graph _ li lo _, Graph _ ri ro _, (mapping, _))) <- copies
        , (l, r) <- zip (li ++ lo) (ri ++ ro)
        ]
    nodes =
      [(i, s) | (i, s) <- zip [0 ..] hs, IS.notMember i deleted]
        ++ concat [zip [start ..] rs | (start, (_, Graph rs _ _ _, _)) <- copies]
    nodeSorts = IM.fromList [(root i, s) | (i, s) <- nodes]
    indices = IM.fromList (zip (IM.keys nodeSorts) [0 ..])
    renumber i = indices IM.! root i
    boxes = retainedBoxes ++ concat [map (fmap (+ start)) rb | (start, (_, Graph _ _ _ rb, _)) <- copies]

portsOf :: Box l n -> [(Int, n)]
portsOf (Box _ ins outs) = [(2 * p, n) | (p, n) <- zip [0 ..] ins] ++ [(2 * p + 1, n) | (p, n) <- zip [0 ..] outs]

type Prepared :: Kind -> Type -> Type
type Prepared s l = (Graph s (LabelTest l), Graph s l, Match)

-- | Bounds on successful rule applications and batches. 'Nothing' leaves that
-- count unrestricted; zero permits checking for a normal form but no applications.
-- These limits do not bound the cost of finding matches.
data RewriteLimits = RewriteLimits
  { maxRewrites :: Maybe Natural
  , maxBatches :: Maybe Natural
  }
  deriving (Eq, Show)

-- | No rewrite or batch limit. Use when the rules are known to terminate, or
-- with the strictly decreasing policy of 'Proarrow.Tools.HypergraphRewrite.compileReducingRules'.
unlimitedRewrites :: RewriteLimits
unlimitedRewrites = RewriteLimits Nothing Nothing

-- | Why normalisation stopped. A normal form has no applicable rule, even when
-- a limit was reached exactly. If both limits prevent further rewriting, the
-- rewrite limit takes precedence.
data NormalisationStatus = NormalForm | RewriteLimitReached | BatchLimitReached
  deriving (Eq, Show)

-- | The current graph and counts of successful rule applications and nonempty
-- batches. Counts and limits are local to this call; the graph can be passed to
-- 'Proarrow.Tools.HypergraphRewrite.normalise' again to continue after exhausting a limit.
type NormalisationResult :: Type -> Type
data NormalisationResult a = NormalisationResult
  { normalisedGraph :: a
  , normalisationStatus :: NormalisationStatus
  , normalisationRewrites :: Natural
  , normalisationBatches :: Natural
  }

normaliseBy
  :: forall {s} l as bs
   . RewriteLimits
  -> (Graph s l -> [Prepared s l])
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> NormalisationResult (Wires as ~> (Wires bs :: OPENHG s l))
normaliseBy limits next host =
  host //
    let result = normaliseGraphBy limits next (graph host)
        Graph ns ins outs boxes = normalisedGraph result
        output = if normalisationBatches result == 0 then host else unsafeOpenHypergraph ns ins outs boxes
    in result{normalisedGraph = output}

normaliseGraphBy
  :: RewriteLimits -> (Graph s l -> [Prepared s l]) -> Graph s l -> NormalisationResult (Graph s l)
normaliseGraphBy limits next = go 0 0
  where
    reached limit count = maybe False (count >=) limit
    go !steps !batches current = case next current of
      [] -> NormalisationResult current NormalForm steps batches
      chosen
        | reached (maxRewrites limits) steps -> NormalisationResult current RewriteLimitReached steps batches
        | reached (maxBatches limits) batches -> NormalisationResult current BatchLimitReached steps batches
        | otherwise ->
            let applied = case maxRewrites limits of
                  Nothing -> chosen
                  Just limit -> genericTake (limit - steps) chosen
                count = fromIntegral (length applied)
            in go (steps + count) (batches + 1) (replaceSelected current applied)
