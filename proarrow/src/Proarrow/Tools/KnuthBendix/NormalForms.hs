{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Regular languages of normal forms for finite typed presentations.
-- After successful completion, avoiding the rules' left sides gives exactly
-- one word per arrow. A finite automaton recognises these words; object types
-- restrict its transitions to composable generators. Declared objects absent
-- from the alphabet are isolated, with just their identity arrow.
module Proarrow.Tools.KnuthBendix.NormalForms
  ( -- * Compilation
    Generator (..)
  , NormalForms
  , compile

    -- * Hom-sets
  , enumerate
  , Cardinality (..)
  , cardinality
  , cardinalitiesFrom
  , cardinalitiesTo
  , renderDot

    -- * Cancellation
  , isEpi
  , isMono
  , EpiMonoFactorization (..)
  , epiMonoFactorization

    -- * Limits and colimits
  , terminalObjects
  , initialObjects
  , Cone (..)
  , Cocone (..)
  , binaryProducts
  , binaryCoproducts
  , Equalizer (..)
  , equalizers
  , Coequalizer (..)
  , coequalizers
  , pullbacks
  , pushouts
  ) where

import Control.Monad (guard)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List (inits, isSuffixOf, tails)
import Data.Map.Strict qualified as M
import Data.Maybe (isJust, listToMaybe, mapMaybe)
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable, eqT)
import Data.Vector qualified as V
import Numeric.Natural (Natural)
import Type.Reflection (SomeTypeRep (..), typeRep)
import Prelude

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..))
import Proarrow.Core (CAT, CategoryOf (..), Ob', Show2)
import Proarrow.Object (SomeOb, SomeOf (..), someRepOf)
import Proarrow.Tools.KnuthBendix qualified as KB

-- Compilation

-- | A generator in the finite alphabet, with evidence for connecting its ports.
-- Reflection is local to this alphabet; completion itself needs only 'EqGen'.
type Generator :: forall {k}. CAT k -> Type
data Generator p where
  Generator :: forall {k} {p :: CAT k} a b. (Ob' a, Ob' b, Typeable a, Typeable b) => p a b -> Generator p

-- | A normal-form acceptor. Its states remember the longest suffix which is
-- a proper prefix of a forbidden word, as in the Aho–Corasick construction.
-- Words are read in execution order, opposite to the displayed path spine.
type NormalForms :: forall {k}. CAT k -> Type
data NormalForms (p :: CAT k) = NormalForms
  { nfObjects :: [SomeOb k]
  , nfSystem :: KB.System p
  , nfAlphabet :: V.Vector (Generator p)
  , nfForward :: Automaton
  , nfBackward :: ~Automaton
  }

-- | Compile a finite object universe, alphabet and successful completion.
-- List all objects, including isolated ones. Every generator endpoint must
-- be declared. Duplicate objects are removed. The alphabet must
-- contain every generator in the completed rules, including their right sides;
-- it may also contain generators absent from the equations. Duplicates are removed.
-- Returns 'Nothing' for an incomplete system, an undeclared endpoint or a
-- missing rule generator.
--
-- >>> import Proarrow.Category.Instance.Unit (Unit(..))
-- >>> import Proarrow.Category.Instance.Paths (pathLength)
-- >>> let done = KB.complete (KB.Limits 4 20) [] :: KB.Completion Unit
-- >>> let forms = maybe (error "compilation failed") id (compile [Some @'()] [Generator Unit] done)
-- >>> cardinality @'() @'() forms
-- Just Infinite
-- >>> fmap (map pathLength . take 4) (enumerate @'() @'() forms)
-- Just [0,1,2,3]
-- >>> let discrete = maybe (error "compilation failed") id (compile [Some @'()] [] done)
-- >>> cardinality @'() @'() discrete
-- Just (Finite 1)
compile :: forall {k} (p :: CAT k). (EqGen p) => [SomeOb k] -> [Generator p] -> KB.Completion p -> Maybe (NormalForms p)
compile _ _ KB.Incomplete{} = Nothing
compile universe supplied (KB.Complete system) = do
  guard (all (\(a, b) -> a `S.member` declared && b `S.member` declared) endpoints)
  patterns <- traverse forbiddenWord (KB.rules system)
  pure
    NormalForms
      { nfObjects = objects
      , nfSystem = system
      , nfAlphabet = alphabet
      , nfForward = buildAutomaton endpoints (map reverse patterns)
      , -- Reversing a normal form preserves avoidance of the reversed patterns.
        nfBackward = buildAutomaton (V.map (\(a, b) -> (b, a)) endpoints) patterns
      }
  where
    objects = nubOrd universe
    declared = S.fromList (map someRepOf objects)
    endpoints = V.map ends alphabet
    alphabet = V.fromList (reverse (foldl' add [] supplied))
    add :: [Generator p] -> Generator p -> [Generator p]
    add seen g@(Generator p)
      | any (\(Generator q) -> isJust (eqGen p q)) seen = seen
      | otherwise = g : seen
    forbiddenWord r = KB.withRule r \lhs rhs -> do
      -- The path spine lists the final generator first.
      keys@(_ : _) <- pathKeys alphabet lhs <* pathKeys alphabet rhs
      pure keys
    ends :: Generator p -> (SomeTypeRep, SomeTypeRep)
    ends (Generator @a @b _) = (SomeTypeRep (typeRep @a), SomeTypeRep (typeRep @b))

-- Hom-sets

-- | Every normal arrow between the requested objects, in nondecreasing word
-- length. Infinite hom-sets are enumerated fairly; finite and empty ones terminate.
-- An undeclared endpoint gives 'Nothing'. Paths are constructed raw, independently of any 'Proarrow.Category.Instance.Paths.Rewrite' instance.
enumerate
  :: forall a b p. (Ob' a, Ob' b, Typeable a, Typeable b) => NormalForms p -> Maybe [(PTH a :: PATHS p) ~> PTH b]
enumerate forms = enumerateGraph @a @b (homGraph @a @b forms) forms <$ checkEndpoints @a @b forms

-- | Number of arrows in a hom-set. 'Infinite' means a cycle lies on an
-- accepted route, not merely that the presentation contains a cycle.
data Cardinality = Finite Natural | Infinite deriving (Eq, Show)

-- | Count the arrows, or return 'Nothing' for an undeclared endpoint.
cardinality
  :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Ob' a, Ob' b, Typeable a, Typeable b) => NormalForms p -> Maybe Cardinality
cardinality forms = countHomSet @a @b forms <$ checkEndpoints @a @b forms

-- | Count all hom-sets out of the given source in one traversal of its
-- reachable automaton. Results follow the declared object order and include
-- empty hom-sets. An undeclared source gives 'Nothing'.
cardinalitiesFrom
  :: forall {k} (a :: k) (p :: CAT k)
   . (Ob' a, Typeable a)
  => NormalForms p -> Maybe [(SomeOb k, Cardinality)]
cardinalitiesFrom forms = countsFrom (nfObjects forms) (nfForward forms) source <$ guard (declares forms source)
  where
    source = SomeTypeRep (typeRep @a)

-- | Count all hom-sets into the given target. Results follow the declared
-- object order and include empty hom-sets. An undeclared target gives 'Nothing'.
cardinalitiesTo
  :: forall {k} (b :: k) (p :: CAT k)
   . (Ob' b, Typeable b)
  => NormalForms p -> Maybe [(SomeOb k, Cardinality)]
cardinalitiesTo forms = countsFrom (nfObjects forms) (nfBackward forms) target <$ guard (declares forms target)
  where
    target = SomeTypeRep (typeRep @b)

-- | Render the productive automaton for @a → b@ as Graphviz DOT. Node labels
-- show the current object and remembered suffix in execution order. An incoming
-- arrow marks the start, and double circles mark states where a word may end.
-- An empty hom-set produces an empty graph. An undeclared endpoint gives 'Nothing'.
renderDot
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (Ob' a, Ob' b, Typeable a, Typeable b, Show2 p)
  => NormalForms p -> Maybe String
renderDot forms@NormalForms{nfAlphabet = alphabet, nfForward = Automaton{automatonStates = states}} = do
  checkEndpoints @a @b forms
  pure $ unlines (["digraph NormalForms {", "  rankdir=LR;"] ++ start ++ nodes ++ edges ++ ["}"])
  where
    graph = homGraph @a @b forms
    numbers = M.fromList (zip (M.keys graph) [0 :: Int ..])
    node s = "n" ++ show (numbers M.! s)
    start = case M.lookup (state @a 0) numbers of
      Nothing -> []
      Just i -> ["  start [shape=point];", "  start -> n" ++ show i ++ ";"]
    nodes =
      [ "  " ++ node s ++ " [label=" ++ quote (show object ++ "\n" ++ suffix s) ++ ", shape=" ++ shape object ++ "];"
      | s@(object, _) <- M.keys graph
      ]
    edges =
      [ "  " ++ node from ++ " -> " ++ node to ++ " [label=" ++ quote (label i) ++ "];"
      | (from, outgoing) <- M.toList graph
      , (i, to) <- outgoing
      ]
    shape object = if object == fst (state @b 0) then "doublecircle" else "circle"
    suffix (_, s) = case fst (states V.! s) of
      [] -> "ε"
      word -> unwords (map label word)
    label i = case alphabet V.! i of Generator g -> show g
    quote value = "\"" ++ concatMap escape value ++ "\""
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape c = [c]

-- Cancellation

-- | Test right cancellation against every object of the compiled presentation.
-- Returns 'Nothing' for an undeclared endpoint, a generator outside the
-- alphabet, or when an infinite hom-set leaves cancellation undecided.
isEpi
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p
  -> (PTH a :: PATHS p) ~> PTH b
  -> Maybe Bool
isEpi forms f = normalisePath forms f >>= isEpiNormal forms

-- | Test left cancellation. The object universe and result have the same
-- interpretation as in 'isEpi'.
isMono
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p
  -> (PTH a :: PATHS p) ~> PTH b
  -> Maybe Bool
isMono forms f = normalisePath forms f >>= isMonoNormal forms

-- | An epic arrow followed by a monic arrow, or a definitive negative result
-- for the declared presentation.
type EpiMonoFactorization :: forall {k}. CAT k -> k -> k -> Type
data EpiMonoFactorization p a b where
  EpiMonoFactorization
    :: forall {k} {p :: CAT k} {a :: k} {b :: k} x
     . (Ob' x, Typeable x)
    => ((PTH a :: PATHS p) ~> PTH x)
    -> ((PTH x :: PATHS p) ~> PTH b)
    -> EpiMonoFactorization p a b
  NoEpiMonoFactorization :: EpiMonoFactorization p a b

-- | Find an epi–mono factorisation, with both legs in normal form. Returns
-- 'Nothing' for an undeclared endpoint, a generator outside the alphabet,
-- or when infinite hom-sets leave the existence of a factorisation undecided.
epiMonoFactorization
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p -> ((PTH a :: PATHS p) ~> PTH b) -> Maybe (EpiMonoFactorization p a b)
epiMonoFactorization forms@NormalForms{nfObjects = objects, nfSystem = system} f = do
  normal <- normalisePath forms f
  foldr (prefer . search normal) noFactorization objects
  where
    noFactorization = Just NoEpiMonoFactorization
    -- A witness settles the query even if other candidates are undecided.
    prefer
      :: Maybe (EpiMonoFactorization p a b) -> Maybe (EpiMonoFactorization p a b) -> Maybe (EpiMonoFactorization p a b)
    prefer found@(Just EpiMonoFactorization{}) _ = found
    prefer (Just NoEpiMonoFactorization) rest = rest
    prefer Nothing found@(Just EpiMonoFactorization{}) = found
    prefer Nothing _ = Nothing
    search :: ((PTH a :: PATHS p) ~> PTH b) -> SomeOb k -> Maybe (EpiMonoFactorization p a b)
    search normal (Some @x)
      | M.null left || M.null right = noFactorization
      | any isCyclic (graphComponents left) || any isCyclic (graphComponents right) = Nothing
      | otherwise =
          foldr
            prefer
            noFactorization
            [ decide e m <$> allDecided [epic, monic]
            | (e, epic) <- leftLegs
            , (m, monic) <- rightLegs
            , composeNormal system m e == normal
            ]
      where
        left = homGraph @a @x forms
        right = homGraph @x @b forms
        leftLegs = [(e, isEpiNormal forms e) | e <- enumerateGraph @a @x left forms]
        rightLegs = [(m, isMonoNormal forms m) | m <- enumerateGraph @x @b right forms]
        decide e m True = EpiMonoFactorization e m
        decide _ _ False = NoEpiMonoFactorization

-- Limits and colimits

-- | Terminal objects of the compiled presentation.
terminalObjects :: forall {k} (p :: CAT k). NormalForms p -> [SomeOb k]
terminalObjects NormalForms{nfObjects = objects, nfForward = forward, nfBackward = backward} =
  findTerminalObjects objects forward backward

-- | Initial objects of the compiled presentation.
initialObjects :: forall {k} (p :: CAT k). NormalForms p -> [SomeOb k]
initialObjects NormalForms{nfObjects = objects, nfForward = forward, nfBackward = backward} =
  findTerminalObjects objects backward forward

-- | A cone with an apex and two outgoing legs, as returned by
-- 'binaryProducts' and 'pullbacks'.
type Cone :: forall {k}. CAT k -> k -> k -> Type
data Cone p a b where
  Cone
    :: forall {k} {p :: CAT k} {a :: k} {b :: k} x
     . (Ob' x, Typeable x)
    => ((PTH x :: PATHS p) ~> PTH a)
    -> ((PTH x :: PATHS p) ~> PTH b)
    -> Cone p a b

-- | A cocone with an apex and two incoming legs, as returned by
-- 'binaryCoproducts' and 'pushouts'.
type Cocone :: forall {k}. CAT k -> k -> k -> Type
data Cocone p a b where
  Cocone
    :: forall {k} {p :: CAT k} {a :: k} {b :: k} x
     . (Ob' x, Typeable x)
    => ((PTH a :: PATHS p) ~> PTH x)
    -> ((PTH b :: PATHS p) ~> PTH x)
    -> Cocone p a b

-- | Find every binary product cone for the given objects, in terms of normal
-- paths. An empty list means no such cone exists in the presentation.
-- Returns 'Nothing' if an endpoint is undeclared or a candidate that passes
-- the hom-set count check requires testing an infinite hom-set.
binaryProducts
  :: forall a b p. (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b) => NormalForms p -> Maybe [Cone p a b]
binaryProducts forms = findProducts @a @b LimitDirection forms Cone

-- | Find every binary coproduct cocone for the given objects. The result has
-- the same interpretation as in 'binaryProducts'.
binaryCoproducts
  :: forall a b p. (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b) => NormalForms p -> Maybe [Cocone p a b]
binaryCoproducts forms = findProducts @a @b ColimitDirection forms Cocone

-- | An equalizer with its apex and inclusion into the source of the parallel arrows.
type Equalizer :: forall {k}. CAT k -> k -> Type
data Equalizer p a where
  Equalizer
    :: forall {k} {p :: CAT k} {a :: k} x
     . (Ob' x, Typeable x)
    => ((PTH x :: PATHS p) ~> PTH a) -> Equalizer p a

-- | Find every equalizer of two parallel paths. Returns 'Nothing' for an
-- undeclared endpoint, a generator outside the alphabet, or an infinite
-- hom-set into the common source that prevents enumerating equalizing arrows.
-- An empty list means no equalizer exists in the declared presentation.
equalizers
  :: forall a b p
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p
  -> ((PTH a :: PATHS p) ~> PTH b)
  -> ((PTH a :: PATHS p) ~> PTH b)
  -> Maybe [Equalizer p a]
equalizers forms f g = findEqualizers @a @b LimitDirection forms f g Equalizer

-- | A coequalizer with its apex and quotient from the target of the parallel arrows.
type Coequalizer :: forall {k}. CAT k -> k -> Type
data Coequalizer p b where
  Coequalizer
    :: forall {k} {p :: CAT k} {b :: k} x
     . (Ob' x, Typeable x)
    => ((PTH b :: PATHS p) ~> PTH x) -> Coequalizer p b

-- | Find every coequalizer of two parallel paths. The result has the dual
-- interpretation to 'equalizers', testing hom-sets out of the common target.
coequalizers
  :: forall a b p
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p
  -> ((PTH a :: PATHS p) ~> PTH b)
  -> ((PTH a :: PATHS p) ~> PTH b)
  -> Maybe [Coequalizer p b]
coequalizers forms f g = findEqualizers @b @a ColimitDirection forms f g Coequalizer

-- | Find every pullback of two paths with a common target. An empty list
-- means no pullback exists. Returns 'Nothing' for an undeclared endpoint,
-- a generator outside the alphabet, or an infinite hom-set that prevents
-- enumerating the pairs of compatible arrows.
pullbacks
  :: forall a b c p
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b, Typeable c)
  => NormalForms p
  -> ((PTH a :: PATHS p) ~> PTH c)
  -> ((PTH b :: PATHS p) ~> PTH c)
  -> Maybe [Cone p a b]
pullbacks forms f g = findPullbacks @a @b @c LimitDirection forms f g Cone

-- | Find every pushout of two paths with a common source. The result has
-- the dual interpretation to 'pullbacks'.
pushouts
  :: forall a b c p
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b, Typeable c)
  => NormalForms p
  -> ((PTH c :: PATHS p) ~> PTH a)
  -> ((PTH c :: PATHS p) ~> PTH b)
  -> Maybe [Cocone p a b]
pushouts forms f g = findPullbacks @a @b @c ColimitDirection forms f g Cocone

-- Automata and graphs

data Automaton = Automaton
  { automatonEndpoints :: V.Vector (SomeTypeRep, SomeTypeRep)
  , automatonStates :: V.Vector ([Int], IM.IntMap Int)
  }

buildAutomaton :: V.Vector (SomeTypeRep, SomeTypeRep) -> [[Int]] -> Automaton
buildAutomaton endpoints patterns = Automaton endpoints states
  where
    prefixes = S.toList (S.fromList ([] : concatMap (init . inits) patterns))
    numbered = M.fromList (zip prefixes [0 ..])
    byLast = IM.fromListWith (++) [(last word, [word]) | word <- patterns]
    step prefix label =
      let candidate = prefix ++ [label]
          -- Any newly completed forbidden word ends with the new generator.
          candidates = IM.findWithDefault [] label byLast
      in if any (`isSuffixOf` candidate) candidates
           then Nothing
           else listToMaybe [s | suffix <- tails candidate, Just s <- [M.lookup suffix numbered]]
    transitions prefix = IM.fromList [(i, s) | i <- [0 .. V.length endpoints - 1], Just s <- [step prefix i]]
    states = V.fromList [(prefix, transitions prefix) | prefix <- prefixes]

declares :: NormalForms p -> SomeTypeRep -> Bool
declares NormalForms{nfObjects = objects} object = any ((== object) . someRepOf) objects

checkEndpoints :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Typeable a, Typeable b) => NormalForms p -> Maybe ()
checkEndpoints forms =
  guard (declares forms (SomeTypeRep (typeRep @a)) && declares forms (SomeTypeRep (typeRep @b)))

pathKeys :: (EqGen p) => V.Vector (Generator p) -> (a :: PATHS p) ~> b -> Maybe [Int]
pathKeys _ PNil = Just []
pathKeys alphabet (PCons p rest) =
  (:) <$> V.findIndex (\(Generator q) -> isJust (eqGen p q)) alphabet <*> pathKeys alphabet rest

type State = (SomeTypeRep, Int)
type Graph = M.Map State [(Int, State)]

state :: forall a. (Typeable a) => Int -> State
state s = (SomeTypeRep (typeRep @a), s)

reachable :: (Ord a) => (a -> [a]) -> [a] -> S.Set a
reachable next = go S.empty
  where
    go seen [] = seen
    go seen (x : pending)
      | S.member x seen = go seen pending
      | otherwise = go (S.insert x seen) (next x ++ pending)

reachableGraph :: Automaton -> State -> Graph
reachableGraph Automaton{automatonEndpoints = ends, automatonStates = transitions} start =
  visit M.empty [start]
  where
    visit graph [] = graph
    visit graph (s : pending)
      | M.member s graph = visit graph pending
      | otherwise =
          let edges = next s
          in visit (M.insert s edges graph) (map snd edges ++ pending)
    next (object, s) =
      [ (i, (target, s'))
      | (i, (source, target)) <- zip [0 ..] (V.toList ends)
      , object == source
      , Just s' <- [IM.lookup i (snd (transitions V.! s))]
      ]

-- Keep only states on a path from the source to an accepting target. Besides
-- avoiding false infinity reports, this makes enumeration of an empty or finite
-- hom-set terminate even when other hom-sets contain cycles.
homGraph :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Typeable a, Typeable b) => NormalForms p -> Graph
homGraph forms =
  M.map (filter (\(_, target) -> S.member target productive)) (M.restrictKeys graph productive)
  where
    graph = reachableGraph (nfForward forms) (state @a 0)
    backwards = M.fromListWith (++) [(target, [source]) | (source, edges) <- M.toList graph, (_, target) <- edges]
    productive = reachable (\s -> M.findWithDefault [] s backwards) [s | s <- M.keys graph, fst s == fst (state @b 0)]

graphComponents :: Graph -> [SCC State]
graphComponents graph = stronglyConnComp [(s, s, map snd edges) | (s, edges) <- M.toList graph]

isCyclic :: SCC a -> Bool
isCyclic CyclicSCC{} = True
isCyclic _ = False

-- Hom-set counting and enumeration

countsFrom :: [SomeOb k] -> Automaton -> SomeTypeRep -> [(SomeOb k, Cardinality)]
countsFrom objects automaton source =
  [(object, M.findWithDefault (Finite 0) (someRepOf object) totals) | object <- objects]
  where
    start = (source, 0)
    perState = countWalks (reachableGraph automaton start) start
    totals = M.fromListWith addCounts [(object, n) | ((object, _), n) <- M.toList perState]

-- The graph contains precisely the states reachable from the given start.
countWalks :: Graph -> State -> M.Map State Cardinality
countWalks graph start = foldl' advance (M.singleton start (Finite 1)) (reverse (graphComponents graph))
  where
    -- Process sources before targets so all incoming paths have been counted
    -- when an acyclic state forwards its count.
    advance counts (AcyclicSCC s) = push (M.findWithDefault (Finite 0) s counts) counts s
    -- Every state in the graph is reachable from a start. A cyclic component
    -- therefore contributes infinitely many paths to itself and its successors.
    advance counts (CyclicSCC ss) = foldl' (push Infinite) (foldr (`M.insert` Infinite) counts ss) ss
    push n counts s = foldl' (\m (_, t) -> M.insertWith addCounts t n m) counts (graph M.! s)

addCounts :: Cardinality -> Cardinality -> Cardinality
addCounts (Finite x) (Finite y) = Finite (x + y)
addCounts _ _ = Infinite

countHomSet :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Typeable a, Typeable b) => NormalForms p -> Cardinality
countHomSet forms
  | any isCyclic components = Infinite
  | otherwise = Finite (M.findWithDefault 0 (state @a 0) (foldl' count M.empty [s | AcyclicSCC s <- components]))
  where
    graph = homGraph @a @b forms
    components = graphComponents graph
    -- stronglyConnComp lists dependencies before their dependants.
    count counts s =
      M.insert s ((if fst s == fst (state @b 0) then 1 else 0) + sum [counts M.! target | (_, target) <- graph M.! s]) counts

type Walk :: forall {k}. CAT k -> k -> Type
data Walk p a where
  Walk :: forall {k} {p :: CAT k} {a :: k} b. (Ob' b, Typeable b) => Int -> (PTH a :: PATHS p) ~> PTH b -> Walk p a

enumerateGraph
  :: forall a b p
   . (Ob' a, Ob' b, Typeable a, Typeable b)
  => Graph -> NormalForms p -> [(PTH a :: PATHS p) ~> PTH b]
enumerateGraph graph NormalForms{nfAlphabet = alphabet}
  | M.member (state @a 0) graph = go [Walk 0 PNil]
  | otherwise = []
  where
    go [] = []
    go layer = mapMaybe accept layer ++ go (concatMap extend layer)
    accept :: Walk p a -> Maybe ((PTH a :: PATHS p) ~> PTH b)
    accept (Walk @x _ p) = case eqT @x @b of
      Just Refl -> Just p
      Nothing -> Nothing
    extend :: Walk p a -> [Walk p a]
    extend (Walk @x s p) =
      [ Walk s' (PCons g p)
      | (i, (_, s')) <- M.findWithDefault [] (state @x s) graph
      , Generator @y g <- [alphabet V.! i]
      , Just Refl <- [eqT @x @y]
      ]

-- Universal property searches

findTerminalObjects :: [SomeOb k] -> Automaton -> Automaton -> [SomeOb k]
findTerminalObjects objects forward backward = filter isTerminal possible
  where
    candidates = filter (reachesAll objects (V.toList (automatonEndpoints backward))) objects
    -- One outgoing row can rule out candidates before counting their incoming arrows.
    possible = case candidates of
      source : _ : _ ->
        let singletons = S.fromList [someRepOf target | (target, Finite 1) <- countsFrom objects forward (someRepOf source)]
        in filter (\target -> someRepOf target `S.member` singletons) candidates
      _ -> candidates
    isTerminal object = all ((== Finite 1) . snd) (countsFrom objects backward (someRepOf object))

-- An unreachable vertex in the generator graph already rules out a candidate.
reachesAll :: [SomeOb k] -> [(SomeTypeRep, SomeTypeRep)] -> SomeOb k -> Bool
reachesAll objects edges = \object ->
  S.size (reachable (\a -> S.toList (M.findWithDefault S.empty a next)) [someRepOf object]) == size
  where
    size = length objects
    next = M.fromListWith S.union [(a, S.singleton b) | (a, b) <- edges]

data ConeDirection op where
  LimitDirection :: ConeDirection False
  ColimitDirection :: ConeDirection True

type ConeLeg :: forall {k}. Bool -> CAT k -> k -> k -> Type
type family ConeLeg op p x a where
  ConeLeg False p x a = (PTH x :: PATHS p) ~> PTH a
  ConeLeg True p x a = (PTH a :: PATHS p) ~> PTH x

findProducts
  :: forall {k} (a :: k) (b :: k) (p :: CAT k) op result
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => ConeDirection op
  -> NormalForms p
  -> (forall x. (Ob' x, Typeable x) => ConeLeg op p x a -> ConeLeg op p x b -> result)
  -> Maybe [result]
findProducts direction forms@NormalForms{nfObjects = objects} witness = do
  checkEndpoints @a @b forms
  findUniversal
    direction
    forms
    [ (object, n, pairedCones @x @a @b direction forms (witness @x) (pairs @x))
    | (object@(Some @x), n) <- zip objects required
    ]
  where
    counts = coneCounts direction forms
    required = zipWith multiplyCounts (counts (fst (state @a 0))) (counts (fst (state @b 0)))
    pairs :: forall x. (Ob' x, Typeable x) => [(ConeLeg op p x a, ConeLeg op p x b)]
    pairs =
      let rightLegs = coneArrows @x @b direction forms
      in [(f, g) | f <- coneArrows @x @a direction forms, g <- rightLegs]

pairedCones
  :: forall {k} (x :: k) (a :: k) (b :: k) (p :: CAT k) op result
   . (EqGen p, Ob' x, Ob' a, Ob' b, Typeable x, Typeable a, Typeable b)
  => ConeDirection op
  -> NormalForms p
  -> (ConeLeg op p x a -> ConeLeg op p x b -> result)
  -> [(ConeLeg op p x a, ConeLeg op p x b)]
  -> [SomeOb k]
  -> [result]
pairedCones direction forms@NormalForms{nfSystem = system} witness pairs probes =
  [witness f g | (f, g) <- pairs, all (\check -> check f g) checks]
  where
    checks = map checkCone probes
    checkCone :: SomeOb k -> ConeLeg op p x a -> ConeLeg op p x b -> Bool
    checkCone (Some @y) =
      let inputs = coneArrows @y @x direction forms
      in case direction of
           LimitDirection -> \f g -> distinct [(composeNormal system f h, composeNormal system g h) | h <- inputs]
           ColimitDirection -> \f g -> distinct [(composeNormal system h f, composeNormal system h g) | h <- inputs]

findEqualizers
  :: forall {k} (a :: k) (b :: k) (p :: CAT k) op result
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => ConeDirection op
  -> NormalForms p
  -> ConeLeg op p a b
  -> ConeLeg op p a b
  -> (forall x. (Ob' x, Typeable x) => ConeLeg op p x a -> result)
  -> Maybe [result]
findEqualizers direction forms@NormalForms{nfObjects = objects, nfSystem = system} f g witness = do
  checkEndpoints @a @b forms
  _ <- coneKeys @a @b direction forms f *> coneKeys @a @b direction forms g
  let totals = coneCounts direction forms (fst (state @a 0))
  guard (Infinite `notElem` totals)
  findUniversal direction forms (map entry objects)
  where
    entry object@(Some @x) =
      let legs = equalizing @x
      in (object, Finite (foldl' (\n _ -> n + 1) 0 legs), cones @x legs)
    equalizing :: forall x. (Ob' x, Typeable x) => [ConeLeg op p x a]
    equalizing = case direction of
      LimitDirection ->
        let nf = KB.normalise system f
            ng = KB.normalise system g
        in filter (\h -> composeNormal system nf h == composeNormal system ng h) (coneArrows @x @a direction forms)
      ColimitDirection ->
        let nf = KB.normalise system f
            ng = KB.normalise system g
        in filter (\h -> composeNormal system h nf == composeNormal system h ng) (coneArrows @x @a direction forms)
    cones :: forall x. (Ob' x, Typeable x) => [ConeLeg op p x a] -> [SomeOb k] -> [result]
    cones legs probes =
      let checks = map (checkCone @x) probes
      in [witness @x e | e <- legs, all ($ e) checks]
    checkCone :: forall x. (Ob' x, Typeable x) => SomeOb k -> ConeLeg op p x a -> Bool
    checkCone (Some @y) =
      let inputs = coneArrows @y @x direction forms
      in case direction of
           LimitDirection -> \e -> distinct [composeNormal system e h | h <- inputs]
           ColimitDirection -> \e -> distinct [composeNormal system h e | h <- inputs]

findPullbacks
  :: forall {k} (a :: k) (b :: k) (c :: k) (p :: CAT k) op result
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b, Typeable c)
  => ConeDirection op
  -> NormalForms p
  -> ConeLeg op p a c
  -> ConeLeg op p b c
  -> (forall x. (Ob' x, Typeable x) => ConeLeg op p x a -> ConeLeg op p x b -> result)
  -> Maybe [result]
findPullbacks direction forms@NormalForms{nfObjects = objects, nfSystem = system} f g witness = do
  checkEndpoints @a @c forms
  checkEndpoints @b @c forms
  _ <- coneKeys @a @c direction forms f *> coneKeys @b @c direction forms g
  guard (Infinite `notElem` upperBounds)
  findUniversal direction forms [entry object n | (object, n) <- zip objects upperBounds]
  where
    counts = coneCounts direction forms
    upperBounds = zipWith multiplyCounts (counts (fst (state @a 0))) (counts (fst (state @b 0)))
    entry object@(Some @x) upperBound =
      let pairs
            | upperBound == Finite 0 = []
            | otherwise = compatible @x
          n = Finite (foldl' (\count _ -> count + 1) 0 pairs)
      in (object, n, pairedCones @x @a @b direction forms (witness @x) pairs)
    compatible :: forall x. (Ob' x, Typeable x) => [(ConeLeg op p x a, ConeLeg op p x b)]
    compatible =
      let left = coneArrows @x @a direction forms
          right = coneArrows @x @b direction forms
      in case direction of
           LimitDirection ->
             matchingPairs (composeNormal system (KB.normalise system f)) (composeNormal system (KB.normalise system g)) left right
           ColimitDirection ->
             matchingPairs
               (\h -> composeNormal system h (KB.normalise system f))
               (\h -> composeNormal system h (KB.normalise system g))
               left
               right

matchingPairs :: (Eq c) => (a -> c) -> (b -> c) -> [a] -> [b] -> [(a, b)]
matchingPairs leftKey rightKey left right =
  [(a, b) | a <- left, let key = leftKey a, (b, other) <- keyedRight, key == other]
  where
    keyedRight = [(b, rightKey b) | b <- right]

coneKeys :: forall a b p op. (EqGen p) => ConeDirection op -> NormalForms p -> ConeLeg op p a b -> Maybe [Int]
coneKeys direction NormalForms{nfAlphabet = alphabet} leg = case direction of
  LimitDirection -> pathKeys alphabet leg
  ColimitDirection -> pathKeys alphabet leg

findUniversal
  :: forall {k} (p :: CAT k) op result
   . ConeDirection op
  -> NormalForms p
  -> [(SomeOb k, Cardinality, [SomeOb k] -> [result])]
  -> Maybe [result]
findUniversal direction forms entries =
  concat <$> traverse search entries
  where
    required = [n | (_, n, _) <- entries]
    probes = [object | (object, n, _) <- entries, n /= Finite 0]
    search (object, _, cones)
      | coneCounts direction forms (someRepOf object) /= required = Just []
      | Infinite `elem` required = Nothing
      -- With equal finite counts, injectivity suffices for a bijection.
      | otherwise = Just (cones probes)

coneCounts :: ConeDirection op -> NormalForms p -> SomeTypeRep -> [Cardinality]
coneCounts direction forms = map snd . countsFrom (nfObjects forms) automaton
  where
    automaton = case direction of
      LimitDirection -> nfBackward forms
      ColimitDirection -> nfForward forms

coneArrows
  :: forall x y p op
   . (Ob' x, Ob' y, Typeable x, Typeable y)
  => ConeDirection op -> NormalForms p -> [ConeLeg op p x y]
coneArrows direction forms = case direction of
  LimitDirection -> enumerateGraph @x @y (homGraph @x @y forms) forms
  ColimitDirection -> enumerateGraph @y @x (homGraph @y @x forms) forms

multiplyCounts :: Cardinality -> Cardinality -> Cardinality
multiplyCounts (Finite x) (Finite y) = Finite (x * y)
multiplyCounts (Finite 0) _ = Finite 0
multiplyCounts _ (Finite 0) = Finite 0
multiplyCounts _ _ = Infinite

-- Cancellation and normal paths

normalisePath
  :: forall a b p
   . (EqGen p, Typeable a, Typeable b)
  => NormalForms p -> ((PTH a :: PATHS p) ~> PTH b) -> Maybe ((PTH a :: PATHS p) ~> PTH b)
normalisePath forms@NormalForms{nfSystem = system, nfAlphabet = alphabet} f = do
  checkEndpoints @a @b forms
  KB.normalise system f <$ pathKeys alphabet f

isEpiNormal
  :: forall a b p. (EqGen p, Ob' b, Typeable b) => NormalForms p -> ((PTH a :: PATHS p) ~> PTH b) -> Maybe Bool
isEpiNormal forms@NormalForms{nfObjects = objects, nfSystem = system} f = allDecided (map cancels objects)
  where
    cancels (Some @x) = checkCancellation @b @x forms (\g -> composeNormal system g f)

isMonoNormal
  :: forall a b p. (EqGen p, Ob' a, Typeable a) => NormalForms p -> ((PTH a :: PATHS p) ~> PTH b) -> Maybe Bool
isMonoNormal forms@NormalForms{nfObjects = objects, nfSystem = system} f = allDecided (map cancels objects)
  where
    cancels (Some @x) = checkCancellation @x @a forms (composeNormal system f)

checkCancellation
  :: forall a b p result
   . (Ob' a, Ob' b, Typeable a, Typeable b, Eq result)
  => NormalForms p -> ((PTH a :: PATHS p) ~> PTH b -> result) -> Maybe Bool
checkCancellation forms compose
  | any isCyclic (graphComponents graph) = Nothing
  | otherwise = Just (distinct (map compose (enumerateGraph @a @b graph forms)))
  where
    graph = homGraph @a @b forms

-- Compose two normal forms using the system that supplied the enumeration.
composeNormal :: KB.System p -> (a :: PATHS p) ~> b -> x ~> a -> x ~> b
composeNormal _ PNil g = g
composeNormal system (PCons f rest) g = KB.rewrite system f (composeNormal system rest g)

distinct :: (Eq a) => [a] -> Bool
distinct [] = True
distinct (x : xs) = x `notElem` xs && distinct xs

allDecided :: [Maybe Bool] -> Maybe Bool
allDecided = foldr combine (Just True)
  where
    combine (Just True) rest = rest
    combine (Just False) _ = Just False
    combine Nothing (Just False) = Just False
    combine Nothing _ = Nothing
