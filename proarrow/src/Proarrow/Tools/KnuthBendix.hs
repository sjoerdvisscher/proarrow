{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Knuth–Bendix completion for typed paths over fixed generators. Associativity
-- is built into 'Paths' spines and identities are empty paths. Rules contain no
-- arrow or object metavariables. Overlaps are the ordinary inclusion and crossing
-- overlaps of words, restricted to composable paths.
--
-- 'complete' numbers generators by first appearance in the presentation.
-- 'completeWithOrder' accepts ordered keys whose equality must agree with
-- 'EqGen'. Shortlex makes every rule decrease, including
-- in surrounding paths. 'Complete' means all nontrivial critical pairs have been
-- processed; under these assumptions its system terminates, is confluent, and
-- presents the input equations. 'Incomplete' retains the outstanding obligations.
-- Rules are interreduced as they are added. Collapsed left sides return to the
-- equation queue, and surviving right sides are normalised.
-- Overlap candidates are indexed by first generators and left-side occurrences.
-- Successful completion compiles a matcher used by 'normalise' and 'rewrite';
-- 'rules' still exposes the completed rules for inspection.
--
-- This is the string-completion procedure described in the
-- <https://gap-packages.github.io/kbmag/doc/chap2.html KBMAG manual>, with typed
-- generators supplying endpoint equalities during matching.
module Proarrow.Tools.KnuthBendix
  ( Equation
  , ProEquation ((:=:))
  , Rule
  , withRule
  , System
  , rules
  , normalise
  , rewrite
  , equivalent
  , Compiled
  , compile
  , normaliseCompiled
  , rewriteCompiled
  , criticalPairs
  , Limits (..)
  , Limit (..)
  , Completion (..)
  , complete
  , completeWithOrder
  ) where

import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Type)
import Data.List (findIndex, sort)
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Type.Equality ((:~:) (..))
import Data.Vector qualified as V
import Prelude

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), pathLength)
import Proarrow.Core (CAT, CategoryOf (Ob))
import Proarrow.Tools.Laws (ProEquation (..))
import Proarrow.Tools.Laws qualified as Laws

type Equation :: forall {k}. CAT k -> Type
type Equation p = ProEquation (Paths :: CAT (PATHS p))

type Rule :: forall {k}. CAT k -> Type
data Rule p where
  Rule :: Paths (a :: PATHS p) b -> Paths a b -> Rule p

withRule :: Rule p -> (forall a b. Paths (a :: PATHS p) b -> Paths a b -> r) -> r
withRule (Rule l r) f = f l r

type System :: forall {k}. CAT k -> Type
data System p where
  System :: (EqGen p) => [Rule p] -> Maybe (Compiled p) -> System p

rules :: System p -> [Rule p]
rules (System rs _) = rs

-- Raw concatenation deliberately bypasses the user's Rewrite instance.
append :: Paths a b -> Paths x a -> Paths x b
append PNil q = q
append (PCons p more) q = PCons p (append more q)

sourceIdentity :: Paths a b -> Paths a a
sourceIdentity PNil = PNil
sourceIdentity (PCons _ more) = sourceIdentity more

comparePaths
  :: forall {k} (p :: CAT k) key a b c d
   . (Ord key) => (forall x y. p x y -> key) -> Paths (a :: PATHS p) b -> Paths (c :: PATHS p) d -> Ordering
comparePaths rank a b = compare (pathLength a) (pathLength b) <> compare (ranks a) (ranks b)
  where
    ranks :: Paths (x :: PATHS p) y -> [key]
    ranks PNil = []
    ranks (PCons p more) = rank p : ranks more

strip :: (EqGen p) => Paths (a :: PATHS p) b -> Paths x b -> Maybe (Paths x a)
strip PNil rest = Just rest
strip (PCons p more) (PCons q rest) = case eqGen p q of
  Just Refl -> strip more rest
  _ -> Nothing
strip _ PNil = Nothing

-- Insert a right-hand side onto a tail that is already normal. Calling the
-- user's Rewrite instance here could select a different system or recurse.
normaliseOnto :: System p -> Paths (a :: PATHS p) b -> Paths x a -> Paths x b
normaliseOnto _ PNil rest = rest
normaliseOnto system (PCons p more) rest = rewrite system p (normaliseOnto system more rest)

rewriteRoot
  :: (EqGen p)
  => (forall x y z. Paths (x :: PATHS p) y -> Paths z x -> Paths z y)
  -> Rule p
  -> Paths (a :: PATHS p) b
  -> Maybe (Paths a b)
rewriteRoot insert (Rule (PCons p more) rhs) (PCons q rest) = case eqGen p q of
  Just Refl -> insert rhs <$> strip more rest
  _ -> Nothing
rewriteRoot _ _ _ = Nothing

-- | Prepend one generator to an already-normal tail, checking only the new
-- boundary. A replacement is inserted incrementally, so redexes created within
-- it or across its boundary are also reduced. Suitable for implementing
-- 'Proarrow.Category.Instance.Paths.Rewrite' instances.
rewrite
  :: (Ob a, Ob b)
  => System p -> p a b -> Paths i (PTH a :: PATHS p) -> Paths i (PTH b)
rewrite (System _ (Just compiled)) p more = rewriteCompiled compiled p more
rewrite system@(System rs Nothing) p more =
  let path = PCons p more
  in fromMaybe path (listToMaybe (mapMaybe (\r -> rewriteRoot (normaliseOnto system) r path) rs))

-- | Normalise a raw path from its input end, reusing each already-normal tail.
-- Every step strictly decreases shortlex. This bypasses the user's
-- 'Proarrow.Category.Instance.Paths.Rewrite' instance; completion inputs should
-- use 'PNil' and 'PCons' to avoid invoking that instance while building its rules.
-- Completed systems use their compiled matcher; incomplete systems scan rules.
normalise :: System p -> Paths (a :: PATHS p) b -> Paths a b
normalise _ PNil = PNil
normalise system (PCons p more) = rewrite system p (normalise system more)

-- | Equality of normal forms. This decides the input equational theory only
-- after 'Complete'; with a partial system it establishes equality when True,
-- but False can mean that completion still needs more rules.
equivalent :: System p -> Paths (a :: PATHS p) b -> Paths a b -> Bool
equivalent system@System{} a b = normalise system a == normalise system b

-- | A fixed system compiled into a prefix trie with integer dispatch.
-- 'Complete' systems already use a compiled matcher through 'normalise' and
-- 'rewrite'. 'compile' also permits compiling an incomplete system explicitly.
type Compiled :: forall {k}. CAT k -> Type
data Compiled p where
  Compiled :: (EqGen p) => GeneratorKey p -> Trie p -> Compiled p

type Trie :: forall {k}. CAT k -> Type
data Trie p = Trie (Maybe (Rule p)) (IM.IntMap (Trie p))

-- | Compile a snapshot of the rules. Ordered keys are used only for dispatch;
-- equal keys must agree with 'EqGen' on rule and future input generators.
-- The result has the same normal forms as 'normalise'. Compiling an incomplete
-- system does not establish confluence or completeness.
--
-- >>> import Proarrow.Category.Instance.Unit (Unit(..))
-- >>> let step = PCons Unit PNil
-- >>> let run s = pathLength (normaliseCompiled (compile (const ()) s) (PCons Unit step))
-- >>> case complete (Limits 4 20) [step :=: PNil] of { Complete s -> run s; Incomplete{} -> -1 }
-- 0
compile :: (Ord key) => (forall a b. p a b -> key) -> System p -> Compiled p
compile rank (System rs _) = compileWithKey (orderedKey rank alphabet) rs
  where
    alphabet = uniqueGenerators [g | Rule l _ <- rs, g <- generators l]

compileWithKey :: (EqGen p) => GeneratorKey p -> [Rule p] -> Compiled p
compileWithKey key rs = Compiled key (build [(leftKeys key r, r) | r <- rs])
  where
    build entries =
      let children = IM.fromListWith (++) [(k, [(more, r)]) | (k : more, r) <- entries]
      in Trie (listToMaybe [r | ([], r) <- entries]) (IM.map build children)

-- Cache the alphabet's ranks and compute the input rank once per trie step.
-- Subsequent branch lookup compares integer keys only.
orderedKey :: (Ord key) => (forall a b. p a b -> key) -> [Generator p] -> GeneratorKey p
orderedKey rank alphabet = \p ->
  let input = rank p
      search lo hi
        | lo >= hi = -1
        | otherwise =
            let mid = (lo + hi) `div` 2
            in case compare input (sorted V.! mid) of
                 LT -> search lo mid
                 EQ -> mid
                 GT -> search (mid + 1) hi
  in search 0 (V.length sorted)
  where
    sorted = V.fromList (sort [rank p | Generator p <- alphabet])

-- Interreduction makes left sides prefix-free, so a terminal cannot shadow
-- another rule. The selected rule is checked again to recover typed endpoints.
matchTrie :: GeneratorKey p -> Trie p -> Paths (a :: PATHS p) b -> Maybe (Rule p)
matchTrie _ (Trie (Just r) _) _ = Just r
matchTrie key (Trie _ branches) (PCons p more) = do
  child <- IM.lookup (key p) branches
  matchTrie key child more
matchTrie _ _ PNil = Nothing

normaliseCompiledOnto :: Compiled p -> Paths (a :: PATHS p) b -> Paths x a -> Paths x b
normaliseCompiledOnto _ PNil rest = rest
normaliseCompiledOnto compiled (PCons p more) rest = rewriteCompiled compiled p (normaliseCompiledOnto compiled more rest)

-- | The compiled counterpart of 'rewrite', with the same already-normal-tail
-- precondition. Suitable for a 'Proarrow.Category.Instance.Paths.Rewrite' instance.
rewriteCompiled
  :: (Ob a, Ob b)
  => Compiled p -> p a b -> Paths i (PTH a :: PATHS p) -> Paths i (PTH b)
rewriteCompiled compiled@(Compiled key trie) p more =
  let path = PCons p more
  in fromMaybe path $ do
       r <- matchTrie key trie path
       rewriteRoot (normaliseCompiledOnto compiled) r path

-- | Normalise with a compiled prefix matcher, bypassing the user's
-- 'Proarrow.Category.Instance.Paths.Rewrite' instance as 'normalise' does.
normaliseCompiled :: Compiled p -> Paths (a :: PATHS p) b -> Paths a b
normaliseCompiled _ PNil = PNil
normaliseCompiled compiled (PCons p more) = rewriteCompiled compiled p (normaliseCompiled compiled more)

-- Every cut leaves a nonempty suffix, so overlaps share at least one generator.
type Cut :: CAT (PATHS p)
data Cut a b where
  Cut :: Paths m b -> Paths a m -> Cut a b

cuts :: Paths a b -> [Cut a b]
cuts PNil = []
cuts whole@(PCons p more) = Cut PNil whole : [Cut (PCons p before) after | Cut before after <- cuts more]

-- Remainders that extend two matching prefixes to their common word.
-- At least one remainder is empty.
type Overlap :: forall {k} {p :: CAT k}. PATHS p -> PATHS p -> PATHS p -> PATHS p -> Type
data Overlap a b c d where
  Overlap :: Paths x a -> Paths x c -> Overlap a b c b

align :: (EqGen p) => Paths (a :: PATHS p) b -> Paths c b -> Maybe (Overlap a b c b)
align PNil q = Just (Overlap q (sourceIdentity q))
align p PNil = Just (Overlap (sourceIdentity p) p)
align (PCons p more) (PCons q rest) = case eqGen p q of
  Just Refl -> do
    Overlap afterP afterQ <- align more rest
    pure (Overlap afterP afterQ)
  _ -> Nothing

overlap :: (EqGen p) => Paths (a :: PATHS p) b -> Paths (c :: PATHS p) d -> Maybe (Overlap a b c d)
overlap (PCons p more) (PCons q rest) = case eqGen p q of
  Just Refl -> do
    Overlap afterP afterQ <- align more rest
    pure (Overlap afterP afterQ)
  _ -> Nothing
overlap _ _ = Nothing

pairs :: (EqGen p) => Rule p -> Rule p -> [Equation p]
pairs (Rule l r) (Rule l' r') = do
  Cut before after <- cuts l
  Overlap afterL afterR <- maybe [] pure (overlap after l')
  let a = append r afterL
      b = append before (append r' afterR)
  if a == b then [] else pure (a :=: b)

-- | All nontrivial, well-typed inclusion and crossing overlaps, including
-- self-overlaps. Symmetric copies can occur. Empty overlaps are independent
-- rewrites and are omitted; empty left sides cannot arise under shortlex.
-- Enumeration order is unspecified.
criticalPairs :: System p -> [Equation p]
criticalPairs (System rs _) = indexedPairs (generatorKey alphabet) rs
  where
    alphabet = uniqueGenerators [g | Rule l _ <- rs, g <- generators l]

-- First-generator buckets select rules whose prefixes can meet a suffix of
-- the query. Occurrence buckets select rules with a suffix starting at the
-- query's first generator. Rule numbers deduplicate candidates contributed
-- by several buckets.
type OverlapIndex :: forall {k}. CAT k -> Type
data OverlapIndex p = OverlapIndex Int (IM.IntMap (IM.IntMap (Rule p))) (IM.IntMap (IM.IntMap (Rule p)))

emptyIndex :: OverlapIndex p
emptyIndex = OverlapIndex 0 IM.empty IM.empty

type GeneratorKey :: forall {k}. CAT k -> Type
type GeneratorKey p = forall a b. p a b -> Int

leftKeys :: GeneratorKey p -> Rule p -> [Int]
leftKeys key (Rule l _) = [key p | Generator p <- generators l]

indexRule :: GeneratorKey p -> Rule p -> OverlapIndex p -> OverlapIndex p
indexRule key r index@(OverlapIndex n starts occurrences) = case leftKeys key r of
  [] -> index
  ks@(first : _) ->
    let entry = IM.singleton n r
        add k = IM.insertWith IM.union k entry
    in OverlapIndex (n - 1) (add first starts) (IS.foldr add occurrences (IS.fromList ks))

overlapsWith :: (EqGen p) => GeneratorKey p -> OverlapIndex p -> Rule p -> [Equation p]
overlapsWith key (OverlapIndex _ starts occurrences) r = case leftKeys key r of
  [] -> []
  ks@(first : _) ->
    let candidates = IM.unions [IM.findWithDefault IM.empty k starts | k <- IS.toList (IS.fromList ks)]
        containers = IM.findWithDefault IM.empty first occurrences
    in concatMap (pairs r) (IM.elems candidates) ++ concatMap (`pairs` r) (IM.elems containers)

indexedPairs :: (EqGen p) => GeneratorKey p -> [Rule p] -> [Equation p]
indexedPairs key = go emptyIndex
  where
    go _ [] = []
    go index (r : rs) = pairs r r ++ overlapsWith key index r ++ go (indexRule key r index) rs

data Limits = Limits {maxRules :: Int, maxEquations :: Int} deriving (Eq, Show)
data Limit = RuleLimit | EquationLimit deriving (Eq, Show)

type Completion :: forall {k}. CAT k -> Type
data Completion p
  = Complete (System p)
  | Incomplete Limit (System p) [Equation p]

-- | Complete using shortlex, numbering generators by first appearance on the
-- left and then right of each input equation, in spine (display) order. Only
-- typed equality is needed; no order or runtime object reflection is required.
-- Reordering the presentation can change the chosen normal forms and the
-- amount of completion work. Normalisation also accepts generators absent
-- from the presentation: they are compared using 'EqGen', not alphabet ranks.
--
-- >>> import Proarrow.Category.Instance.Unit (Unit(..))
-- >>> let step = PCons Unit PNil
-- >>> case complete (Limits 4 20) [step :=: PNil] of { Complete s -> pathLength (normalise s (PCons Unit step)); Incomplete{} -> -1 }
-- 0
complete :: forall {k} (p :: CAT k). (EqGen p) => Limits -> [Equation p] -> Completion p
complete limits equations = completeWithAlphabet alphabet key key limits equations
  where
    alphabet = presentationAlphabet equations
    key :: GeneratorKey p
    key = generatorKey alphabet

type Generator :: forall {k}. CAT k -> Type
data Generator p where
  Generator :: p a b -> Generator p

generators :: Paths (a :: PATHS p) b -> [Generator p]
generators PNil = []
generators (PCons p more) = Generator p : generators more

presentationAlphabet :: (EqGen p) => [Equation p] -> [Generator p]
presentationAlphabet = uniqueGenerators . concatMap (\e -> Laws.withSides e (\l r -> generators l ++ generators r))

uniqueGenerators :: (EqGen p) => [Generator p] -> [Generator p]
uniqueGenerators = reverse . foldl' add []
  where
    add seen g@(Generator p)
      | any (\(Generator q) -> isJust (eqGen p q)) seen = seen
      | otherwise = g : seen

generatorKey :: (EqGen p) => [Generator p] -> GeneratorKey p
generatorKey alphabet p = fromMaybe (-1) (findIndex (\(Generator q) -> isJust (eqGen p q)) alphabet)

-- Reduce old rules against a newly oriented rule. Old left sides were already
-- irreducible by each other, so only the new rule can make one collapsible.
-- A changed right side may expose further reductions by the old system.
interreduce :: Rule p -> System p -> (System p, [Equation p], Bool)
interreduce new (System old _) =
  let single = System [new] Nothing
      combined = System (new : old) Nothing
      reduce oldRule@(Rule l r) (kept, pending, changed) =
        let l' = normalise single l
        in if l' /= l
             then (kept, (l' :=: r) : pending, True)
             else
               let r' = normalise single r
               in if r' == r
                    then (oldRule : kept, pending, changed)
                    else (Rule l (normalise combined r') : kept, pending, True)
      (survivors, collapsed, changedRules) = foldr reduce ([], [], False) old
  in (System (new : survivors) Nothing, collapsed, changedRules)

-- | Complete with ordered generator keys. Equal keys must mean that 'eqGen'
-- succeeds, including equality of both endpoints. Shorter paths always come
-- first; equal lengths compare keys from the output end of the spine.
-- Both limits include the initial presentation; maxEquations counts processed
-- obligations, including ones that already join. A limit result retains its
-- partial rules and all unprocessed equations, including collapsed rules.
-- The rule limit applies to the active, interreduced system.
-- Successful completion compiles a matcher whose alphabet lookup also uses
-- the supplied keys on future input generators, consistently with 'EqGen'.
completeWithOrder :: (EqGen p, Ord key) => (forall a b. p a b -> key) -> Limits -> [Equation p] -> Completion p
completeWithOrder rank limits equations = completeWithAlphabet alphabet rank (orderedKey rank alphabet) limits equations
  where
    alphabet = presentationAlphabet equations

completeWithAlphabet
  :: forall {k} (p :: CAT k) key
   . (EqGen p, Ord key)
  => [Generator p] -> (forall a b. p a b -> key) -> GeneratorKey p -> Limits -> [Equation p] -> Completion p
completeWithAlphabet alphabet rank dispatchKey limits equations = go 0 False (System [] Nothing) emptyIndex equations id
  where
    -- All derived generators occur in the presentation. An unknown generator
    -- would share a fallback bucket; pairs still checks typed equality.
    key :: GeneratorKey p
    key = generatorKey alphabet
    -- Each finite batch is exhausted before adding the recheck it requested.
    -- New obligations form the next batch, so rechecks cannot be starved by
    -- continuously generated equations. A difference list avoids queue copying.
    recheck changed system = if changed then indexedPairs key (rules system) else []
    stop reason changed system pending next =
      Incomplete reason system (pending ++ next (recheck changed system))
    go n changed system index [] next = case next (recheck changed system) of
      [] ->
        let rs = rules system
            compiled = compileWithKey dispatchKey rs
        in compiled `seq` Complete (System rs (Just compiled))
      pending -> go n False system index pending id
    go n changed system index pending@(equation : rest) next
      | n >= max 0 (maxEquations limits) = stop EquationLimit changed system pending next
      | otherwise = Laws.withSides equation $ \l r ->
          let a = normalise system l
              b = normalise system r
          in case comparePaths rank a b of
               EQ -> go (n + 1) changed system index rest next
               direction ->
                 let new = if direction == GT then Rule a b else Rule b a
                     (reduced, collapsed, simplified) = interreduce new system
                     -- interreduce retains the new rule at the head. Every new
                     -- overlap is checked; changed old rules are covered by the
                     -- full recheck at the end of this batch.
                     oldIndex = if simplified then foldr (indexRule key) emptyIndex (drop 1 (rules reduced)) else index
                     additions = pairs new new ++ overlapsWith key oldIndex new
                 in if length (rules reduced) > max 0 (maxRules limits)
                      then stop RuleLimit changed system pending next
                      else
                        go (n + 1) (changed || simplified) reduced (indexRule key new oldIndex) rest (next . (collapsed ++) . (additions ++))
