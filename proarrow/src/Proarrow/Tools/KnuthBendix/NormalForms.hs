{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Regular languages of normal forms for finite typed presentations.
-- After successful completion, avoiding the rules' left sides gives exactly
-- one word per arrow. A finite automaton recognises these words; object types
-- restrict its transitions to composable generators. Declared objects absent
-- from the alphabet are isolated, with just their identity arrow.
module Proarrow.Tools.KnuthBendix.NormalForms
  ( Generator (..)
  , NormalForms
  , compile
  , enumerate
  , Cardinality (..)
  , cardinality
  , renderDot
  , initialObjects
  , terminalObjects
  , isEpi
  , isMono
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
  , nfEndpoints :: V.Vector (SomeTypeRep, SomeTypeRep)
  , nfStates :: V.Vector ([Int], IM.IntMap Int)
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
  let prefixes = S.toList (S.fromList ([] : concatMap (init . inits) patterns))
      numbered = M.fromList (zip prefixes [0 ..])
      step prefix label =
        let candidate = prefix ++ [label]
        in if any (`isSuffixOf` candidate) patterns
             then Nothing
             else listToMaybe [s | suffix <- tails candidate, Just s <- [M.lookup suffix numbered]]
      transitions prefix = IM.fromList [(i, s) | i <- [0 .. V.length alphabet - 1], Just s <- [step prefix i]]
      states = V.fromList [(prefix, transitions prefix) | prefix <- prefixes]
  pure
    NormalForms
      { nfObjects = objects
      , nfSystem = system
      , nfAlphabet = alphabet
      , nfEndpoints = endpoints
      , nfStates = states
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
    forbiddenWord r = KB.withRule r \lhs rhs ->
      reverse <$> pathKeys alphabet lhs <* pathKeys alphabet rhs
    ends :: Generator p -> (SomeTypeRep, SomeTypeRep)
    ends (Generator @a @b _) = (SomeTypeRep (typeRep @a), SomeTypeRep (typeRep @b))

checkEndpoints :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Typeable a, Typeable b) => NormalForms p -> Maybe ()
checkEndpoints NormalForms{nfObjects = objects} =
  guard (SomeTypeRep (typeRep @a) `elem` declared && SomeTypeRep (typeRep @b) `elem` declared)
  where
    declared = map someRepOf objects

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

-- Keep only states on a path from the source to an accepting target. Besides
-- avoiding false infinity reports, this makes enumeration of an empty or finite
-- hom-set terminate even when other hom-sets contain cycles.
homGraph :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Typeable a, Typeable b) => NormalForms p -> Graph
homGraph NormalForms{nfEndpoints = ends, nfStates = transitions} =
  M.map (filter (\(_, target) -> S.member target productive)) (M.restrictKeys graph productive)
  where
    next (object, s) =
      [ (i, (target, s'))
      | (i, (source, target)) <- zip [0 ..] (V.toList ends)
      , object == source
      , Just s' <- [IM.lookup i (snd (transitions V.! s))]
      ]
    graph = M.fromSet next (reachable (map snd . next) [state @a 0])
    backwards = M.fromListWith (++) [(target, [source]) | (source, edges) <- M.toList graph, (_, target) <- edges]
    productive = reachable (\s -> M.findWithDefault [] s backwards) [s | s <- M.keys graph, fst s == fst (state @b 0)]

-- | Render the productive automaton for @a → b@ as Graphviz DOT. Node labels
-- show the current object and remembered suffix in execution order. An incoming
-- arrow marks the start, and double circles mark states where a word may end.
-- An empty hom-set produces an empty graph. An undeclared endpoint gives 'Nothing'.
renderDot
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (Ob' a, Ob' b, Typeable a, Typeable b, Show2 p)
  => NormalForms p -> Maybe String
renderDot forms@NormalForms{nfAlphabet = alphabet, nfStates = states} = do
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

-- | Number of arrows in a hom-set. 'Infinite' means a cycle lies on an
-- accepted route, not merely that the presentation contains a cycle.
data Cardinality = Finite Natural | Infinite deriving (Eq, Show)

-- | Count the arrows, or return 'Nothing' for an undeclared endpoint.
cardinality
  :: forall {k} (a :: k) (b :: k) (p :: CAT k). (Ob' a, Ob' b, Typeable a, Typeable b) => NormalForms p -> Maybe Cardinality
cardinality forms = countHomSet @a @b forms <$ checkEndpoints @a @b forms

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

graphComponents :: Graph -> [SCC State]
graphComponents graph = stronglyConnComp [(s, s, map snd edges) | (s, edges) <- M.toList graph]

isCyclic :: SCC a -> Bool
isCyclic CyclicSCC{} = True
isCyclic _ = False

type Walk :: forall {k}. CAT k -> k -> Type
data Walk p a where
  Walk :: forall {k} {p :: CAT k} {a :: k} b. (Ob' b, Typeable b) => Int -> (PTH a :: PATHS p) ~> PTH b -> Walk p a

-- | Every normal arrow between the requested objects, in nondecreasing word
-- length. Infinite hom-sets are enumerated fairly; finite and empty ones terminate.
-- An undeclared endpoint gives 'Nothing'. Paths are constructed raw, independently of any 'Proarrow.Category.Instance.Paths.Rewrite' instance.
enumerate
  :: forall a b p. (Ob' a, Ob' b, Typeable a, Typeable b) => NormalForms p -> Maybe [(PTH a :: PATHS p) ~> PTH b]
enumerate forms = enumerateGraph @a @b (homGraph @a @b forms) forms <$ checkEndpoints @a @b forms

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

-- | Initial objects of the compiled presentation.
initialObjects :: forall {k} (p :: CAT k). NormalForms p -> [SomeOb k]
initialObjects forms@NormalForms{nfObjects = objects} = filter isInitial objects
  where
    isInitial (Some @x) = all (\(Some @y) -> countHomSet @x @y forms == Finite 1) objects

-- | Terminal objects of the compiled presentation.
terminalObjects :: forall {k} (p :: CAT k). NormalForms p -> [SomeOb k]
terminalObjects forms@NormalForms{nfObjects = objects} = filter isTerminal objects
  where
    isTerminal (Some @y) = all (\(Some @x) -> countHomSet @x @y forms == Finite 1) objects

-- | Test right cancellation against every object of the compiled presentation.
-- Returns 'Nothing' for an undeclared endpoint, a generator outside the
-- alphabet, or when an infinite hom-set leaves cancellation undecided.
isEpi
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p
  -> (PTH a :: PATHS p) ~> PTH b
  -> Maybe Bool
isEpi forms@NormalForms{nfObjects = objects, nfSystem = system, nfAlphabet = alphabet} f = do
  checkEndpoints @a @b forms
  _ <- pathKeys alphabet f
  allDecided (map cancels objects)
  where
    normal = KB.normalise system f
    cancels (Some @x) = checkCancellation @b @x forms (\g -> composeNormal system g normal)

-- | Test left cancellation. The object universe and result have the same
-- interpretation as in 'isEpi'.
isMono
  :: forall {k} (a :: k) (b :: k) (p :: CAT k)
   . (EqGen p, Ob' a, Ob' b, Typeable a, Typeable b)
  => NormalForms p
  -> (PTH a :: PATHS p) ~> PTH b
  -> Maybe Bool
isMono forms@NormalForms{nfObjects = objects, nfSystem = system, nfAlphabet = alphabet} f = do
  checkEndpoints @a @b forms
  _ <- pathKeys alphabet f
  allDecided (map cancels objects)
  where
    normal = KB.normalise system f
    cancels (Some @x) = checkCancellation @x @a forms (composeNormal system normal)

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
allDecided results
  | Just False `elem` results = Just False
  | otherwise = and <$> sequence results
