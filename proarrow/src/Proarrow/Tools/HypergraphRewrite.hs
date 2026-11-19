{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Rewriting of open hypergraphs, modulo Frobenius wiring, with individual
-- rules or a compiled discrimination net sharing matching work across rules.
-- A rule's common boundary is the interface retained when replacing its left side.
-- Fixed-pattern matches are injective on nodes and box occurrences. The left boundary must also
-- be injective; the right boundary may join interface nodes. This is a restricted
-- DPO rewriting operation, not a general pushout-complement search for DPOI.
module Proarrow.Tools.HypergraphRewrite
  ( Rule
  , rule
  , Parameter (Literal, Variable)
  , mapParameter
  , parameterRule
  , subgraphRule
  , subgraphRuleWithDirection
  , withSortParameters
  , Port (..)
  , PortGraph (..)
  , portRule
  , parameterPortRule
  , parameterPortRuleWith
  , rewrites
  , rewriteBatch
  , CompiledRules
  , compileRules
  , compileReducingRules
  , rewritesCompiled
  , rewriteBatchCompiled
  , RewriteLimits (..)
  , unlimitedRewrites
  , NormalisationStatus (..)
  , NormalisationResult (..)
  , normalise
  , Direction (..)
  , ruleWith
  , ruleWithDirection
  , parameterRuleWith
  , parameterRuleWithDirection
  , parameterRulesWith
  , rewritesWith
  , rewritesWithDirection
  ) where

import Control.Monad (foldM, unless, void, when)
import Data.Containers.ListUtils (nubOrd)
import Data.Either (isRight)
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Type)
import Data.List (genericTake, mapAccumL, maximumBy, sortOn)
import Data.Map.Strict qualified as M
import Data.Maybe (maybeToList)
import Data.Ord (comparing)
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
  , WireSorts
  , Wires
  , hypergraphParts
  , sameSort
  , unsafeOpenHypergraph
  )
import Proarrow.Core (CategoryOf (..), Kind, (//))
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Tools.Laws (Equation, Law (..), LawBody, Laws (..), lawName, withSides)

-- | Orient an equation as written in its 'Law' body, or in reverse.
data Direction = LeftToRight | RightToLeft
  deriving (Eq, Show)

-- | Select a law left-to-right, using an explicit interpretation to choose its
-- object variables, supplied arrows, and representation of the structures.
-- Unknown and ambiguous law names are errors. The interpreted equation must
-- satisfy 'rule'\'s restriction on the oriented left boundary.
--
-- The interpretation receives the polymorphic body. Instantiate it in a
-- diagram category supporting the requested structures, then use 'withSides'
-- to lower both sides to parallel open hypergraphs. Supplied arrows are concrete;
-- this does not introduce variables matching arbitrary subdiagrams.
ruleWith
  :: forall cs s l
   . (Laws cs)
  => String
  -> (LawBody cs -> Equation (OPENHG s l))
  -> Either String (Rule s l)
ruleWith name = ruleWithDirection @cs name LeftToRight

-- | Like 'ruleWith', with an explicit choice of direction.
ruleWithDirection
  :: forall cs s l
   . (Laws cs)
  => String
  -> Direction
  -> (LawBody cs -> Equation (OPENHG s l))
  -> Either String (Rule s l)
ruleWithDirection name direction interpret = do
  equation <- interpretLaw @cs name interpret
  withSides equation $ \lhs rhs -> case direction of
    LeftToRight -> rule lhs rhs
    RightToLeft -> rule rhs lhs

-- | Select a law left-to-right with the label parameters of 'parameterRule'.
-- The interpretation supplies named arrows as boxes labelled with 'Variable',
-- and structural operations as fixed constructors or 'Literal' fields.
-- Repeated names must bind equal values; the right side reuses those bindings.
-- Object choices and box arities remain fixed, and variables do not match subdiagrams.
-- Compile once, then apply with 'rewrites' or include in 'compileRules'.
parameterRuleWith
  :: forall cs s f a
   . (Laws cs, Traversable f, Eq (f ()), Typeable f, Eq a)
  => String
  -> (LawBody cs -> Equation (OPENHG s (f (Parameter a))))
  -> Either String (Rule s (f a))
parameterRuleWith name = parameterRuleWithDirection @cs name LeftToRight

-- | Like 'parameterRuleWith', with an explicit choice of direction.
-- Parameters on the oriented right side must be bound on the oriented left side.
parameterRuleWithDirection
  :: forall cs s f a
   . (Laws cs, Traversable f, Eq (f ()), Typeable f, Eq a)
  => String
  -> Direction
  -> (LawBody cs -> Equation (OPENHG s (f (Parameter a))))
  -> Either String (Rule s (f a))
parameterRuleWithDirection name direction interpret = do
  equation <- interpretLaw @cs name interpret
  withSides equation $ \lhs rhs -> case direction of
    LeftToRight -> parameterRule lhs rhs
    RightToLeft -> parameterRule rhs lhs

-- | Instantiate every law left-to-right with 'parameterRuleWith', retaining its
-- name for 'compileRules'. Duplicate law names and invalid rules are errors.
parameterRulesWith
  :: forall cs s f a
   . (Laws cs, Traversable f, Eq (f ()), Typeable f, Eq a)
  => (LawBody cs -> Equation (OPENHG s (f (Parameter a))))
  -> Either String [(String, Rule s (f a))]
parameterRulesWith interpret = traverse instantiate (laws @cs)
  where
    instantiate law = do
      let name = lawName law
      r <- parameterRuleWith @cs name interpret
      pure (name, r)

interpretLaw
  :: forall cs k
   . (Laws cs)
  => String -> (LawBody cs -> Equation k) -> Either String (Equation k)
interpretLaw name interpret = case filter ((== name) . lawName) (laws @cs) of
  [] -> Left ("ruleWith: unknown law " ++ show name)
  [Law _ body] -> Right (interpret (\ @a @b @c @d @e mor -> body @a @b @c @d @e mor))
  _ -> Left ("ruleWith: ambiguous law " ++ show name)

-- | Select an explicitly instantiated law left-to-right and enumerate its single-step rewrites.
-- Compile once with 'ruleWith' when applying the same instantiation to several hosts.
rewritesWith
  :: forall cs s l a b
   . (Laws cs, Eq l, DecidableIso s)
  => String
  -> (LawBody cs -> Equation (OPENHG s l))
  -> (a :: OPENHG s l) ~> b
  -> Either String [Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l)]
rewritesWith name = rewritesWithDirection @cs name LeftToRight

-- | Like 'rewritesWith', with an explicit choice of direction.
rewritesWithDirection
  :: forall cs s l a b
   . (Laws cs, Eq l, DecidableIso s)
  => String
  -> Direction
  -> (LawBody cs -> Equation (OPENHG s l))
  -> (a :: OPENHG s l) ~> b
  -> Either String [Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l)]
rewritesWithDirection name direction interpret host =
  fmap (`rewrites` host) (ruleWithDirection @cs name direction interpret)

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

-- | Select a law with the whole-arrow parameters of 'subgraphRule'.
subgraphRuleWithDirection
  :: forall cs s p l
   . (Laws cs)
  => String
  -> Direction
  -> (p -> Either l String)
  -> (LawBody cs -> Equation (OPENHG s p))
  -> Either String (Rule s l)
subgraphRuleWithDirection name direction classify interpret = do
  equation <- interpretLaw @cs name interpret
  withSides equation $ \lhs rhs -> case direction of
    LeftToRight -> subgraphRule classify lhs rhs
    RightToLeft -> subgraphRule classify rhs lhs

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

-- | All valid single-step rewrites, in box and node enumeration order.
-- Works for closed hosts (empty boundaries) as well as open hosts. No result
-- deletes a node used by an unmatched box or the host boundary. Unmatched nodes,
-- including isolated nodes, are retained. Distinct matches may produce isomorphic results;
-- results are not deduplicated. Matching is a finite exhaustive search.
-- Compatible label/arity candidates are cached per pattern box, and mapped
-- ports constrain later boxes through incidence indices. Labels only need 'Eq'.
rewrites
  :: forall {s} l a b
   . (Eq l, DecidableIso s)
  => Rule s l
  -> (a :: OPENHG s l) ~> b
  -> [Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l)]
rewrites (Rule lhs instantiate) host =
  let g = graph host
  in host //
       [ unsafeOpenHypergraph nodes ins outs boxes
       | (match, labels) <- matches lhs g
       , Just rhs <- [instantiate labels]
       , let Graph nodes ins outs boxes = replaceMany lhs rhs g [match]
       ]
rewrites r host = map snd (rewritesCompiled (either error id (compileRules [((), r)])) host)

-- | Apply a greedy maximal set of non-conflicting matches of one rule from a
-- single host snapshot, rebuilding the graph once. Returns the number applied
-- and the result, or @(0, host)@ when the rule does not match.
--
-- Matches are considered in the same order as 'rewrites'. They may share
-- preserved interface nodes, including adjacent regions connected through those
-- nodes. They cannot share boxes, or delete a node used by another chosen match.
-- Each replacement gets fresh nodes and all interfaces are glued simultaneously.
-- This selects one maximal batch, not a maximum-size batch or all possible batches.
-- New matches created by replacement are left for a later batch.
rewriteBatch
  :: forall {s} l as bs
   . (Eq l, DecidableIso s)
  => Rule s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> (Int, Wires as ~> (Wires bs :: OPENHG s l))
rewriteBatch (Rule lhs instantiate) host =
  let g = graph host
      candidates = [(rhs, match) | (match, labels) <- matches lhs g, Just rhs <- [instantiate labels]]
      chosen = nonConflictingBy (\_ (m, _) -> deletedImages lhs m) candidates
  in case chosen of
       [] -> (0, host)
       _ ->
         host //
           let Graph nodes ins outs boxes = replaceSelected g [(lhs, rhs, match) | (rhs, match) <- chosen]
           in (length chosen, unsafeOpenHypergraph nodes ins outs boxes)
rewriteBatch r host = rewriteBatchCompiled (either error id (compileRules [((), r)])) host

-- | Rules compiled into a discrimination net of box-selection and port-binding
-- tests. Common prefixes share their matching work. Graph-node bindings add
-- repeated-wire, sort, and injectivity checks to the usual discrimination-net
-- construction for many-to-one term matching; see
-- <https://arxiv.org/abs/1710.06915 MatchPy: A Pattern Matching Library>.
-- A single host index is shared by every rule in one matching pass.
--
-- Keys identify rules and give an explicit conflict priority: smaller keys win.
-- The order of the input list does not affect matching or batch selection.
type CompiledRules :: Type -> Kind -> Type -> Type
data CompiledRules key s l = CompiledRules (V.Vector (key, Rule s l)) (V.Vector (Signature l)) (Net s) Bool

data Arity = Exactly Int | AtLeast Int deriving (Eq)

type Signature :: Type -> Type
data Signature l = Signature (LabelTest l) Arity Arity

portArity :: [Port] -> Arity
portArity ps = if any capture ps then AtLeast minimumSize else Exactly minimumSize
  where
    minimumSize = length [() | Node _ <- ps]
    capture Capture{} = True
    capture _ = False

acceptsArity :: Arity -> Int -> Bool
acceptsArity (Exactly n) m = n == m
acceptsArity (AtLeast n) m = n <= m

instance (Eq l) => Eq (Signature l) where
  Signature a i o == Signature b i' o' = i == i' && o == o' && sameLabelTest a b

-- Registers name pattern nodes in order of first encounter, independent of the
-- pattern's node numbering. Separate selection from binding so patterns with
-- different repeated-wire constraints still share their gate dispatch.
type Step :: Kind -> Type
data Step s
  = SelectBox Int [Hint]
  | BindPort Bool Int Int (Maybe (SomeSort s))
  | SelectNode Bool Int (Maybe (SomeSort s))
  | BindPorts [PortTest s] [PortTest s]
  | CheckSubgraphs [(Int, Int)]

-- Position-free incidence hints anchor connections after a variable prefix.
data Hint = AtPort Int Int | Incident Int deriving (Eq)

type PortTest :: Kind -> Type
data PortTest s = TestNode Int (Maybe (SomeSort s)) | TestCapture String

-- Original-node to register map, and traversal positions in original box order.
data Terminal = Terminal Int (IM.IntMap Int) [Int]

type Net :: Kind -> Type
data Net s = Net [Terminal] [(Step s, Net s)]

-- | Compile uniquely keyed rules. Box traversal favours connected boxes and
-- then boxes with more fixed ports; fixed arity breaks ties.
-- This anchors a mux before its constant inputs and fixed edges before captures.
-- Common tests are inserted into a discrimination trie, including bindings for
-- isolated nodes and separate searches for disconnected pattern components.
-- Literal labels dispatch by equality; parameter labels dispatch by constructor
-- and fixed fields. Bindings are checked separately for each rule at a terminal.
-- Compilation also compares sorts up to isomorphism. Rules using
-- 'withSortParameters' defer sort validation to their terminals.
compileRules
  :: (Ord key, Eq l, DecidableIso s)
  => [(key, Rule s l)] -> Either String (CompiledRules key s l)
compileRules = compileRuleSet False

-- | Compile rules with a strictly decreasing box-count policy. A candidate is
-- accepted only when its instantiated replacement has fewer boxes than the
-- matched region. This check precedes batch selection, so a rejected candidate
-- cannot block a competing reduction. Parameters and dynamically constructed
-- replacements are checked per match; compilation does not certify that every
-- application of the supplied rules decreases.
--
-- Every application removes at least one box, and compatible batches cannot
-- share boxes. Consequently 'normalise' with 'unlimitedRewrites' terminates on
-- finite hosts after at most the initial number of boxes in rule applications,
-- assuming replacement callbacks terminate. Matching is still an exhaustive
-- finite search and may be expensive. Confluence is not guaranteed.
--
-- Equal-sized changes, including relabelling, and growing replacements are
-- excluded, even if semantically useful. 'NormalForm' means no decreasing
-- application remains; other applications of the original rules may exist.
--
-- >>> let before = unsafeOpenHypergraph [] [] [] [Box "x" [] []] :: (Wires '[] :: OPENHG () String) ~> Wires '[]
-- >>> let after = unsafeOpenHypergraph [] [] [] [] :: (Wires '[] :: OPENHG () String) ~> Wires '[]
-- >>> let r = either error id (rule before after)
-- >>> let compiled = either error id (compileReducingRules [((), r)])
-- >>> let result = normalise unlimitedRewrites compiled before
-- >>> (normalisationStatus result, normalisationRewrites result)
-- (NormalForm,1)
compileReducingRules
  :: (Ord key, Eq l, DecidableIso s)
  => [(key, Rule s l)] -> Either String (CompiledRules key s l)
compileReducingRules = compileRuleSet True

compileRuleSet
  :: (Ord key, Eq l, DecidableIso s)
  => Bool -> [(key, Rule s l)] -> Either String (CompiledRules key s l)
compileRuleSet reducing entries
  | S.size (S.fromList (map fst entries)) /= length entries = Left "compileRules: duplicate rule key"
  | otherwise = Right (CompiledRules rules signatures net reducing)
  where
    rules = V.fromList (sortOn fst entries)
    signatures = V.fromList (foldl' add [] [signature b | (_, r) <- V.toList rules, let PortGraph _ _ bs = rulePattern r, b <- bs])
    add xs x = if x `elem` xs then xs else xs ++ [x]
    paths = [compilePattern signatures i r | (i, (_, r)) <- zip [0 ..] (V.toList rules)]
    net = foldl' (\n (steps, terminal) -> insertNet steps terminal n) (Net [] []) paths

signature :: Box (LabelTest l) Port -> Signature l
signature (Box l ins outs) = Signature l (portArity ins) (portArity outs)

portsOf :: Box l n -> [(Int, n)]
portsOf (Box _ ins outs) = [(2 * p, n) | (p, n) <- zip [0 ..] ins] ++ [(2 * p + 1, n) | (p, n) <- zip [0 ..] outs]

compilePattern :: (Eq l) => V.Vector (Signature l) -> Int -> Rule s l -> ([Step s], Terminal)
compilePattern signatures index ruleToCompile =
  let (steps, registers, order) = boxes IM.empty (zip [0 :: Int ..] bs)
      (allRegisters, isolated) = mapAccumL isolatedNode registers [n | n <- [0 .. length ns - 1], IM.notMember n registers]
      boxRegisters = map snd (sortOn fst (zip order [0 ..]))
  in (steps ++ checks registers ++ concat isolated, Terminal index allRegisters boxRegisters)
  where
    PortGraph ns _ bs = rulePattern ruleToCompile
    aliases = hasSubgraphs ruleToCompile
    arrowHoles = holes ruleToCompile
    sorts = V.fromList (map testSort ns)
    testSort = case ruleToCompile of
      SortRule{} -> const Nothing
      _ -> Just
    register m n = case IM.lookup n m of
      Just r -> (m, r)
      Nothing -> let r = IM.size m in (IM.insert n r m, r)
    checks m = case [(a', b') | (a, b) <- arrowHoles, Just a' <- [IM.lookup a m], Just b' <- [IM.lookup b m]] of
      [] -> []
      connected -> [CheckSubgraphs connected]
    holes (SubgraphRule (Graph _ _ _ patternBoxes) _) = [(a, b) | Box (Right _) [a] [b] <- patternBoxes]
    holes (SortRule _ r) = holes r
    holes _ = []
    isolatedNode m n = let (m', r) = register m n in (m', SelectNode aliases r (sorts V.! n) : checks m')
    boxes m [] = ([], m, [])
    boxes m remaining =
      let score (_, candidate@(Box _ candidateIns candidateOuts)) =
            ( length [() | (_, Node n) <- portsOf candidate, IM.member n m]
            , length [() | (_, Node _) <- portsOf candidate]
            , case (portArity candidateIns, portArity candidateOuts) of (Exactly _, Exactly _) -> True; _ -> False
            )
          (i, b@(Box _ ins outs)) = maximumBy (comparing (\entry@(j, _) -> (score entry, negate j))) remaining
          sig = case V.findIndex (== signature b) signatures of
            Just s -> s
            Nothing -> error "compilePattern: missing signature"
          hints = hintsFor False ins ++ hintsFor True outs
          hintsFor out ps = go 0 True ps
            where
              go _ _ [] = []
              go p positioned (Node n : more) =
                [if positioned then AtPort (2 * p + if out then 1 else 0) r else Incident r | Just r <- [IM.lookup n m]]
                  ++ go (p + 1) positioned more
              go p _ (_ : more) = go p False more
          bind regs (Node n) = let (regs', r) = register regs n in (regs', TestNode r (sorts V.! n))
          bind regs (Capture name) = (regs, TestCapture name)
          bind _ Element{} = error "compilePattern: Element on the left"
          (m1, testsIn) = mapAccumL bind m ins
          (m', testsOut) = mapAccumL bind m1 outs
          fixed p (TestNode r s) = BindPort aliases p r s
          fixed _ TestCapture{} = error "compilePattern: capture in fixed pattern"
          bindings = case (portArity ins, portArity outs) of
            (Exactly _, Exactly _) -> zipWith fixed [0, 2 ..] testsIn ++ zipWith fixed [1, 3 ..] testsOut
            _ -> [BindPorts testsIn testsOut]
          (rest, result, order) = boxes m' [entry | entry@(j, _) <- remaining, j /= i]
      in (SelectBox sig hints : bindings ++ rest, result, i : order)

insertNet :: (DecidableIso s) => [Step s] -> Terminal -> Net s -> Net s
insertNet [] terminal (Net terminals branches) = Net (terminal : terminals) branches
insertNet (step : rest) terminal (Net terminals branches) = Net terminals (insert branches)
  where
    insert [] = [(step, insertNet rest terminal (Net [] []))]
    insert ((test, next) : more)
      | sameStep step test = (test, insertNet rest terminal next) : more
      | otherwise = (test, next) : insert more

sameStep :: (DecidableIso s) => Step s -> Step s -> Bool
sameStep (SelectBox a hints) (SelectBox b hints') = a == b && hints == hints'
sameStep (BindPort a p r s) (BindPort a' p' r' s') = a == a' && p == p' && r == r' && sameSortTest s s'
sameStep (SelectNode a r s) (SelectNode a' r' s') = a == a' && r == r' && sameSortTest s s'
sameStep (CheckSubgraphs a) (CheckSubgraphs b) = a == b
sameStep (BindPorts is os) (BindPorts is' os') = sameTests is is' && sameTests os os'
  where
    sameTests [] [] = True
    sameTests (TestNode r s : xs) (TestNode r' s' : ys) = r == r' && sameSortTest s s' && sameTests xs ys
    sameTests (TestCapture a : xs) (TestCapture b : ys) = a == b && sameTests xs ys
    sameTests _ _ = False
sameStep _ _ = False

sameSortTest :: (DecidableIso s) => Maybe (SomeSort s) -> Maybe (SomeSort s) -> Bool
sameSortTest Nothing Nothing = True
sameSortTest (Just a) (Just b) = sameSort a b
sameSortTest _ _ = False

-- Incidence and signature buckets cache their lengths for candidate selection.
type HostIndex :: Kind -> Type -> Type
data HostIndex s l = HostIndex
  { indexedSorts :: V.Vector (SomeSort s)
  , indexedBoxes :: V.Vector (Box l Int)
  , indexedSignatures :: V.Vector IS.IntSet
  , indexedCandidates :: V.Vector (Int, [Int])
  , indexedIncidence :: V.Vector (IM.IntMap (Int, [Int]))
  , indexedNeighbours :: V.Vector (Int, [Int])
  , indexedBoundary :: IS.IntSet
  }

indexHost :: (Eq l) => V.Vector (Signature l) -> Graph s l -> HostIndex s l
indexHost signatures (Graph ns ins outs bs) = HostIndex (V.fromList ns) (V.fromList bs) ids candidates incidence neighbours (IS.fromList (ins ++ outs))
  where
    -- A host label may satisfy both an exact signature and a constructor key.
    -- Classify it once per snapshot, with exact-label lookup kept separate.
    exact =
      M.fromListWith
        (++)
        [((a, b), [(l, i)]) | (i, Signature (ExactLabel l) (Exactly a) (Exactly b)) <- zip [0 :: Int ..] (V.toList signatures)]
    other = [(test, a, b, i) | (i, Signature test a b) <- zip [0 :: Int ..] (V.toList signatures), not (literalFixed test a b)]
    literalFixed ExactLabel{} (Exactly _) (Exactly _) = True
    literalFixed _ _ _ = False
    classify (Box l a b) =
      let shape = (length a, length b)
      in IS.fromList
           ( maybe [] pure (lookup l (M.findWithDefault [] shape exact))
               ++ [ i
                  | (test, arityIn, arityOut, i) <- other
                  , acceptsArity arityIn (length a)
                  , acceptsArity arityOut (length b)
                  , acceptsLabel test l
                  ]
           )
    ids = V.fromList (map classify bs)
    bucket xs = (length xs, reverse xs)
    candidates =
      V.map
        bucket
        ( V.accum
            (flip (:))
            (V.replicate (V.length signatures) [])
            [(s, i) | (i, matches') <- zip [0 ..] (V.toList ids), s <- IS.toList matches']
        )
    incidence =
      V.map (IM.map bucket) $
        V.accum
          (\m (p, i) -> IM.insertWith (++) p [i] m)
          (V.replicate (length ns) IM.empty)
          [(n, (p, i)) | (i, b) <- zip [0 ..] bs, (p, n) <- portsOf b]

    neighbours = V.map (bucket . IS.toDescList . IS.fromList . concatMap snd . IM.elems) incidence

-- Register bindings, their range, selected boxes in reverse traversal order,
-- and their set for injectivity and dangling checks.
type SearchState = (IM.IntMap Int, IS.IntSet, [Int], IS.IntSet, M.Map String [Int])

runStep :: (DecidableIso s) => HostIndex s l -> Step s -> SearchState -> [SearchState]
runStep host (SelectBox sig hints) (m, range, order, used, captures) =
  [ (m, range, i : order, IS.insert i used, captures)
  | i <- snd (foldl' smaller (indexedCandidates host V.! sig) constrained)
  , IS.notMember i used
  , IS.member sig (indexedSignatures host V.! i)
  ]
  where
    constrained = map constrain hints
    constrain (AtPort p r) = IM.findWithDefault (0, []) p (indexedIncidence host V.! (m IM.! r))
    constrain (Incident r) = indexedNeighbours host V.! (m IM.! r)
    smaller a b = if fst a <= fst b then a else b
runStep host (BindPort aliases p r sort) state@(_, _, order, _, _) = case order of
  i : _ ->
    let Box _ ins outs = indexedBoxes host V.! i
        n = (if even p then ins else outs) !! (p `div` 2)
    in maybe [] pure (bindNode aliases host r sort n state)
  [] -> error "runStep: port test without a box"
runStep host (SelectNode aliases r sort) state =
  [next | n <- [0 .. V.length (indexedSorts host) - 1], Just next <- [bindNode aliases host r sort n state]]
runStep host (CheckSubgraphs holes) state@(m, _, _, used, _) =
  [state | all (\(a, b) -> not (null (captureRegions host (IS.fromList (IM.elems m)) used (m IM.! a) (m IM.! b)))) holes]
runStep host (BindPorts ins outs) state@(_, _, order, _, _) = case order of
  i : _ -> let Box _ is os = indexedBoxes host V.! i in matchPorts ins is state >>= matchPorts outs os
  [] -> error "runStep: port capture without a box"
  where
    matchPorts [] [] current = [current]
    matchPorts (TestNode r sort : more) (n : rest) current =
      maybe [] (matchPorts more rest) (bindNode False host r sort n current)
    matchPorts [TestCapture name] nodes current@(m, range, chosen, used, captures) =
      case M.lookup name captures of
        Just bound -> [current | bound == nodes]
        Nothing -> [(m, range, chosen, used, M.insert name nodes captures)]
    matchPorts (TestCapture name : more) nodes current@(m, range, chosen, used, captures) =
      case M.lookup name captures of
        Just bound -> [next | take (length bound) nodes == bound, next <- matchPorts more (drop (length bound) nodes) current]
        Nothing ->
          [ next
          | size <- case more of
              TestNode r _ : _
                | Just expected <- IM.lookup r m ->
                    [i | (i, n) <- zip [0 ..] nodes, n == expected]
              _ -> [0 .. length nodes]
          , let (prefix, rest) = splitAt size nodes
          , next <- matchPorts more rest (m, range, chosen, used, M.insert name prefix captures)
          ]
    matchPorts _ _ _ = []

bindNode
  :: (DecidableIso s) => Bool -> HostIndex s l -> Int -> Maybe (SomeSort s) -> Int -> SearchState -> Maybe SearchState
bindNode aliases host r sort n state@(m, range, order, used, captures)
  | Just n' <- IM.lookup r m = if n == n' then Just state else Nothing
  | not aliases && IS.member n range = Nothing
  | maybe False (\expected -> not (sameSort expected (indexedSorts host V.! n))) sort = Nothing
  | otherwise = Just (IM.insert r n m, IS.insert n range, order, used, captures)

type Prepared :: Kind -> Type -> Type
type Prepared s l = (Graph s (LabelTest l), Graph s l, Match)

compiledMatches :: (Eq l, DecidableIso s) => CompiledRules key s l -> Graph s l -> [(Int, Prepared s l)]
compiledMatches (CompiledRules rules signatures net reducing) g =
  [ (i, prepared)
  | (i, _, _, prepared) <-
      sortOn
        (\(i, order, m, _) -> (i, order, IM.elems m))
        (walk net (IM.empty, IS.empty, [], IS.empty, M.empty))
  ]
  where
    host = indexHost signatures g
    walk (Net terminals branches) state@(registers, _, order, used, captures) =
      [ (i, originalOrder, mapping, prepared)
      | Terminal i originalNodes boxRegisters <- terminals
      , let mapping = IM.map (registers IM.!) originalNodes
            (_, r) = rules V.! i
            originalOrder = map (boxImages V.!) boxRegisters
      , prepared@(lhs, Graph _ _ _ replacement, (nodes, selected)) <-
          prepareMatch host r mapping used captures originalOrder
      , not reducing || length replacement < IS.size selected
      , all (deletable nodes selected) (internalNodes lhs)
      ]
        ++ [result | (step, next) <- branches, state' <- runStep host step state, result <- walk next state']
      where
        boxImages = V.fromList (reverse order)
    deletable m used x =
      let y = m IM.! x
      in IS.notMember y (indexedBoundary host)
           && all (\(_, boxes) -> all (`IS.member` used) boxes) (IM.elems (indexedIncidence host V.! y))

prepareMatch
  :: (Eq l, DecidableIso s)
  => HostIndex s l -> Rule s l -> IM.IntMap Int -> IS.IntSet -> M.Map String [Int] -> [Int] -> [Prepared s l]
prepareMatch host (Rule lhs instantiate) mapping used _ order = maybeToList $ do
  rhs <- instantiate [label (indexedBoxes host V.! i) | i <- order]
  pure (lhs, rhs, (mapping, used))
prepareMatch host (PortRule (PortGraph ns interface _) instantiate) mapping used captures order = maybeToList $ do
  PortGraph rs rightInterface rightBoxes <- instantiate captures (map label selected)
  let captured = nubOrd (concat (M.elems captures))
      kept = nubOrd (map (mapping IM.!) interface ++ captured)
      deleted = [mapping IM.! n | n <- [0 .. length ns - 1], n `notElem` interface]
  -- A captured alias must remain alive, even if it also matched a numbered node.
  unless (all (`notElem` captured) deleted) Nothing
  let nodes = nubOrd (IM.elems mapping ++ captured)
      leftIndices = IM.fromList (zip nodes [0 ..])
      interfaceMap = IM.fromList (zip (map (mapping IM.!) interface) rightInterface)
      extra = [n | n <- captured, IM.notMember n interfaceMap]
      rightIndices = IM.union interfaceMap (IM.fromList (zip extra [length rs ..]))
      port (Node n) = Just [n]
      port (Capture name) = map (rightIndices IM.!) <$> M.lookup name captures
      port (Element name i) = do
        values <- M.lookup name captures
        if i >= 0 && i < length values then Just [rightIndices IM.! (values !! i)] else Nothing
      expand ps = concat <$> traverse port ps
      left =
        Graph
          [indexedSorts host V.! n | n <- nodes]
          [leftIndices IM.! n | n <- kept]
          []
          [fmap (leftIndices IM.!) (Box (ExactLabel l) is os) | Box l is os <- selected]
      rightSorts = rs ++ [indexedSorts host V.! n | n <- extra]
  boxes <- traverse (\(Box l is os) -> Box l <$> expand is <*> expand os) rightBoxes
  pure (left, Graph rightSorts [rightIndices IM.! n | n <- kept] [] boxes, (IM.fromList (zip [0 ..] nodes), used))
  where
    selected = [indexedBoxes host V.! i | i <- order]
prepareMatch host (SubgraphRule lhs rhs) mapping used _ _ =
  prepareSubgraphs host lhs rhs mapping used
prepareMatch host (SortRule instantiate (SubgraphRule lhs (Graph rs ri ro rb))) mapping used _ _ = do
  let Graph ls _ _ _ = lhs
      actual = [indexedSorts host V.! (mapping IM.! n) | n <- [0 .. length ls - 1]]
  sorts <- maybeToList (instantiate ls actual rs)
  if length sorts == length rs
    then prepareSubgraphs host lhs (Graph sorts ri ro rb) mapping used
    else []
prepareMatch host (SortRule instantiate r) mapping used captures order = do
  (Graph ls li lo lb, Graph rs ri ro rb, match@(images, _)) <- prepareMatch host r mapping used captures order
  maybeToList $ do
    let PortGraph patternSorts _ _ = rulePattern r
        actual = [indexedSorts host V.! (mapping IM.! n) | n <- [0 .. length patternSorts - 1]]
        leftSorts = [indexedSorts host V.! (images IM.! n) | n <- [0 .. length ls - 1]]
    rightSorts <- instantiate patternSorts actual rs
    unless (length rightSorts == length rs) Nothing
    unless (length li + length lo == length ri + length ro) Nothing
    unless (and [sameSort (leftSorts !! l) (rightSorts !! r') | (l, r') <- zip (li ++ lo) (ri ++ ro)]) Nothing
    pure (Graph leftSorts li lo lb, Graph rightSorts ri ro rb, match)

-- Pattern nodes delimit captures. Outside those cuts, every incident box must
-- belong to the same region; the final dangling check protects host boundaries
-- and connections to fixed boxes. No arbitrary subsets of a region are searched.
prepareSubgraphs
  :: (Eq l, DecidableIso s)
  => HostIndex s l
  -> Graph s (Either l String)
  -> Graph s (Either l String)
  -> IM.IntMap Int
  -> IS.IntSet
  -> [Prepared s l]
prepareSubgraphs host (Graph _ li lo lb) rhs mapping fixed = do
  let holes = [(name, a, b) | Box (Right name) [a] [b] <- lb]
      aliases = unionFind [(a, b) | (_, a, b) <- holes, mapping IM.! a == mapping IM.! b]
      groups = IM.fromListWith IS.union [(image, IS.singleton (aliases n)) | (n, image) <- IM.toList mapping]
  -- Only identity substitution may identify distinct pattern nodes.
  unless (all ((== 1) . IS.size) (IM.elems groups)) []
  (environment, selected) <- foldM capture (M.empty, fixed) holes
  -- An unanchored identity would have no box occurrence to locate the rule.
  -- In particular, terminal uniqueness must not expand every terminal wire.
  when (IS.null selected) []
  replacement@(Graph rs ri ro _) <- maybeToList (instantiateSubgraphs rhs environment)
  let nodes = IS.toAscList (IS.unions (IS.fromList (IM.elems mapping) : map boxNodes (IS.toList selected)))
      indices = IM.fromList (zip nodes [0 ..])
      leftSorts = map (indexedSorts host V.!) nodes
      ins = map ((indices IM.!) . (mapping IM.!)) li
      outs = map ((indices IM.!) . (mapping IM.!)) lo
      leftPlain =
        Graph
          leftSorts
          ins
          outs
          [fmap (indices IM.!) (indexedBoxes host V.! i) | i <- IS.toList selected]
      left = mapLabels ExactLabel leftPlain
  unless (length ins + length outs == length ri + length ro) []
  unless (and [sameSort (leftSorts !! a) (rs !! b) | (a, b) <- zip (ins ++ outs) (ri ++ ro)]) []
  when (sameGraph leftPlain replacement) []
  pure (left, replacement, (IM.fromList (zip [0 ..] nodes), selected))
  where
    cuts = IS.fromList (IM.elems mapping)
    boxNodes i = let b = indexedBoxes host V.! i in IS.fromList (inputs b ++ outputs b)
    capture (env, used) (name, a, b) = do
      let input = mapping IM.! a
          output = mapping IM.! b
      region <- captureRegions host cuts used input output
      let nodes = IS.toAscList (IS.insert input (IS.insert output (IS.unions (map boxNodes (IS.toList region)))))
          indices = IM.fromList (zip nodes [0 ..])
          captured =
            Graph
              (map (indexedSorts host V.!) nodes)
              [indices IM.! input]
              [indices IM.! output]
              [fmap (indices IM.!) (indexedBoxes host V.! i) | i <- IS.toList region]
      case M.lookup name env of
        Just previous -> unless (sameGraph previous captured) []
        Nothing -> pure ()
      pure (M.insert name captured env, IS.union used region)

-- Once endpoints are known, grow from an incident box until a cut is reached.
-- Every internal incidence belongs to the region; this also prevents a capture
-- from crossing another capture's interior or a host boundary.
captureRegions :: HostIndex s l -> IS.IntSet -> IS.IntSet -> Int -> Int -> [IS.IntSet]
captureRegions host cuts used input output
  | input == output = [IS.empty]
  | otherwise =
      [ region
      | region <- nubOrd [visit IS.empty [seed] | seed <- snd (indexedNeighbours host V.! input), IS.notMember seed used]
      , let nodes = IS.unions (map boxNodes (IS.toList region))
            interior = IS.difference nodes cuts
      , IS.intersection cuts nodes == IS.fromList [input, output]
      , boundaryPorts region input == [False]
      , boundaryPorts region output == [True]
      , IS.disjoint interior (indexedBoundary host)
      , all (\n -> all (`IS.member` region) (snd (indexedNeighbours host V.! n))) (IS.toList interior)
      ]
  where
    boxNodes i = let b = indexedBoxes host V.! i in IS.fromList (inputs b ++ outputs b)
    visit seen [] = seen
    visit seen (i : pending)
      | IS.member i seen || IS.member i used = visit seen pending
      | otherwise =
          visit
            (IS.insert i seen)
            (concat [snd (indexedNeighbours host V.! n) | n <- IS.toList (IS.difference (boxNodes i) cuts)] ++ pending)
    boundaryPorts region node =
      [odd p | i <- IS.toList region, (p, n) <- portsOf (indexedBoxes host V.! i), n == node]

sameGraph :: (Eq l, DecidableIso s) => Graph s l -> Graph s l -> Bool
sameGraph lhs@(Graph ls li lo lb) rhs@(Graph rs ri ro rb) =
  length ls == length rs
    && length lb == length rb
    && any (\((m, _), _) -> map (m IM.!) li == ri && map (m IM.!) lo == ro) (matches (mapLabels ExactLabel lhs) rhs)

instantiateSubgraphs
  :: (DecidableIso s)
  => Graph s (Either l String) -> M.Map String (Graph s l) -> Maybe (Graph s l)
instantiateSubgraphs (Graph ns ins outs bs) env = do
  captures <- traverse (\(name, a, b) -> (a,b,) <$> M.lookup name env) [(name, a, b) | Box (Right name) [a] [b] <- bs]
  let (_, copies) = mapAccumL (\offset (a, b, g@(Graph sorts _ _ _)) -> (offset + length sorts, (offset, a, b, g))) (length ns) captures
      root = unionFind (concat [[(a, offset + i), (b, offset + o)] | (offset, a, b, Graph _ [i] [o] _) <- copies])
      numbered = zip [0 ..] ns ++ concat [zip [offset ..] sorts | (offset, _, _, Graph sorts _ _ _) <- copies]
      nodeSorts = IM.fromList [(root n, s) | (n, s) <- numbered]
      indices = IM.fromList (zip (IM.keys nodeSorts) [0 ..])
      renumber = (indices IM.!) . root
      boxes =
        [Box l i o | Box (Left l) i o <- bs]
          ++ concat [map (fmap (+ offset)) boxes' | (offset, _, _, Graph _ _ _ boxes') <- copies]
  unless (all (\(n, s) -> sameSort s (nodeSorts IM.! root n)) numbered) Nothing
  pure (Graph (IM.elems nodeSorts) (map renumber ins) (map renumber outs) (map (fmap renumber) boxes))

-- | Enumerate every valid match of every compiled rule, returning its key and
-- single-step result. Results are ordered by key, then by the original rule's
-- box and node enumeration order, as in 'rewrites'. Matching work is shared;
-- overlapping matches and isomorphic results are retained.
rewritesCompiled
  :: forall {s} key l a b
   . (Eq l, DecidableIso s)
  => CompiledRules key s l
  -> (a :: OPENHG s l) ~> b
  -> [(key, Wires (WireSorts a) ~> (Wires (WireSorts b) :: OPENHG s l))]
rewritesCompiled compiled@(CompiledRules rules _ _ _) host =
  host //
    [ (key, unsafeOpenHypergraph ns ins outs bs)
    | (i, (lhs, rhs, match)) <- compiledMatches compiled g
    , let (key, _) = rules V.! i
          Graph ns ins outs bs = replaceMany lhs rhs g [match]
    ]
  where
    g = graph host

-- | Match the entire compiled rule set on one snapshot and apply one greedy
-- maximal batch across rules. Smaller keys have conflict priority; matches of
-- one rule follow 'rewrites' order. Compatible matches of different rules share
-- the batch and the result is rebuilt once. Sharing and deletion conditions are
-- the same as in 'rewriteBatch'. New matches wait for a subsequent batch.
rewriteBatchCompiled
  :: forall {s} key l as bs
   . (Eq l, DecidableIso s)
  => CompiledRules key s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> (Int, Wires as ~> (Wires bs :: OPENHG s l))
rewriteBatchCompiled compiled host =
  let g = graph host
      chosen = batchMatches compiled g
  in case chosen of
       [] -> (0, host)
       _ ->
         host //
           let Graph ns ins outs bs = replaceSelected g chosen
           in (length chosen, unsafeOpenHypergraph ns ins outs bs)

-- | Bounds on successful rule applications and batches. 'Nothing' leaves that
-- count unrestricted; zero permits checking for a normal form but no applications.
-- These limits do not bound the cost of finding matches.
data RewriteLimits = RewriteLimits
  { maxRewrites :: Maybe Natural
  , maxBatches :: Maybe Natural
  }
  deriving (Eq, Show)

-- | No rewrite or batch limit. Use when the rules are known to terminate, or
-- with the strictly decreasing policy of 'compileReducingRules'.
unlimitedRewrites :: RewriteLimits
unlimitedRewrites = RewriteLimits Nothing Nothing

-- | Why normalisation stopped. A normal form has no applicable rule, even when
-- a limit was reached exactly. If both limits prevent further rewriting, the
-- rewrite limit takes precedence.
data NormalisationStatus = NormalForm | RewriteLimitReached | BatchLimitReached
  deriving (Eq, Show)

-- | The current graph and counts of successful rule applications and nonempty
-- batches. Counts and limits are local to this call; the graph can be passed to
-- 'normalise' again to continue after exhausting a limit.
type NormalisationResult :: Type -> Type
data NormalisationResult a = NormalisationResult
  { normalisedGraph :: a
  , normalisationStatus :: NormalisationStatus
  , normalisationRewrites :: Natural
  , normalisationBatches :: Natural
  }

-- | Repeatedly apply compatible batches from the compiled rule set. Matches
-- created by one batch are considered on the next snapshot. Conflict priorities
-- are those of 'compileRules'. A rewrite limit can truncate a batch to its first
-- compatible matches, so neither limit is exceeded.
--
-- Stopping at a limit probes for further matches to distinguish exhaustion from
-- a normal form, without applying another rewrite. Ordinary rules do not compare
-- graphs: reproducing the left side still counts as an application and needs a
-- limit. Subgraph rules skip structurally identical replacements. Arbitrary
-- rule sets may not terminate with 'unlimitedRewrites';
-- 'compileReducingRules' excludes all non-decreasing applications.
normalise
  :: forall {s} key l as bs
   . (Eq l, DecidableIso s)
  => RewriteLimits
  -> CompiledRules key s l
  -> (Wires as :: OPENHG s l) ~> Wires bs
  -> NormalisationResult (Wires as ~> (Wires bs :: OPENHG s l))
normalise limits compiled host =
  host //
    let finish status steps batches (Graph ns ins outs boxes) =
          NormalisationResult
            (if batches == 0 then host else unsafeOpenHypergraph ns ins outs boxes)
            status
            steps
            batches
        go !steps !batches current = case batchMatches compiled current of
          [] -> finish NormalForm steps batches current
          chosen
            | reached (maxRewrites limits) steps -> finish RewriteLimitReached steps batches current
            | reached (maxBatches limits) batches -> finish BatchLimitReached steps batches current
            | otherwise ->
                let applied = case maxRewrites limits of
                      Nothing -> chosen
                      Just limit -> genericTake (limit - steps) chosen
                    count = fromIntegral (length applied)
                in go (steps + count) (batches + 1) (replaceSelected current applied)
    in go 0 0 (graph host)
  where
    reached limit count = maybe False (count >=) limit

batchMatches :: (Eq l, DecidableIso s) => CompiledRules key s l -> Graph s l -> [Prepared s l]
batchMatches compiled g =
  [ (lhs, rhs, match)
  | ((lhs, rhs), match) <-
      nonConflictingBy
        (\(lhs, _) (m, _) -> deletedImages lhs m)
        [((lhs, rhs), match) | (_, (lhs, rhs, match)) <- compiledMatches compiled g]
  ]

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
