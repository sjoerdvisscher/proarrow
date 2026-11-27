-- | Compile and run the discrimination net for many-to-one graph matching.
module Proarrow.Tools.HypergraphRewrite.Internal.Matcher
  ( CompiledRules (..)
  , compileRuleSet
  , compiledMatches
  , compiledMatchesAvoiding
  , compiledMatchesWithMaps
  , compiledHasPortMaps
  ) where

import Control.Monad (foldM, unless, when)
import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.Kind (Type)
import Data.List (mapAccumL, maximumBy, sortOn)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe, listToMaybe, maybeToList)
import Data.Ord (comparing)
import Data.Set qualified as S
import Data.Vector qualified as V
import Prelude

import Proarrow.Category.Instance.FinHask (unionFind)
import Proarrow.Category.Instance.OpenHypergraph (Box (..), SomeSort, sameSort)
import Proarrow.Core (Kind)
import Proarrow.Optic.Iso (DecidableIso)
import Proarrow.Tools.HypergraphRewrite.Internal
  ( CaptureEnd (..)
  , Graph (..)
  , LabelTest (..)
  , Port (..)
  , PortGraph (..)
  , PortReplacement (MappedPorts)
  , Prepared
  , Rule (..)
  , acceptsLabel
  , hasSubgraphs
  , instantiatePorts
  , internalNodes
  , mapLabels
  , portsOf
  , rulePattern
  , sameGraph
  , sameLabelTest
  )

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
  | SelectRepeatedLink Int
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

compilePattern :: (Eq l) => V.Vector (Signature l) -> Int -> Rule s l -> ([Step s], Terminal)
compilePattern signatures index ruleToCompile =
  let (steps, registers, order) = boxes Nothing IM.empty (zip [0 :: Int ..] bs)
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
    boxes _ m [] = ([], m, [])
    boxes linked m remaining =
      let score (_, candidate@(Box _ candidateIns candidateOuts)) =
            ( length [() | (_, Node n) <- portsOf candidate, IM.member n m]
            , length [() | (_, Node _) <- portsOf candidate]
            , case (portArity candidateIns, portArity candidateOuts) of (Exactly _, Exactly _) -> True; _ -> False
            )
          (i, b@(Box _ ins outs)) = fromMaybe (maximumBy (comparing (\entry@(j, _) -> (score entry, negate j))) remaining) linked
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
          (selection, second) = case linked of
            Just _ -> (SelectRepeatedLink sig, Nothing)
            Nothing -> (SelectBox sig hints, if aliases || length bs /= 4 then Nothing else repeatedLink i b remaining)
          (rest, result, order) = boxes second m' [entry | entry@(j, _) <- remaining, j /= i]
      in (selection : bindings ++ rest, result, i : order)

-- Bind the numbered endpoints of both links before splitting captures on
-- the two boxes they connect. The second link has the same signature.
repeatedLink
  :: (Eq l)
  => Int
  -> Box (LabelTest l) Port
  -> [(Int, Box (LabelTest l) Port)]
  -> Maybe (Int, Box (LabelTest l) Port)
repeatedLink first link remaining = case linkNodes link of
  Just ends
    | length others == 3 ->
        listToMaybe
          [ entry
          | entry@(second, candidate) <- others
          , signature candidate == signature link
          , Just secondEnds <- [linkNodes candidate]
          , IS.disjoint ends secondEnds
          , let neighbours = [box | (i, box) <- others, i /= second]
          , all variadicEndpoints neighbours
          , [a, b] <- [map numberedNodes neighbours]
          , covers ends a b && covers secondEnds a b
          ]
  _ -> Nothing
  where
    others = filter ((/= first) . fst) remaining
    -- Keep both variadic boxes in their original capture enumeration order.
    variadicEndpoints (Box _ ins outs) = case (portArity ins, portArity outs) of
      (Exactly _, Exactly _) -> False
      (i, o) -> minimumArity i + minimumArity o == 2
    minimumArity (Exactly n) = n
    minimumArity (AtLeast n) = n
    numberedNodes box = IS.fromList [n | (_, Node n) <- portsOf box]
    linkNodes box = case map snd (portsOf box) of
      [Node a, Node b] | a /= b -> Just (IS.fromList [a, b])
      _ -> Nothing
    covers ends a b =
      let l = IS.intersection ends a
          r = IS.intersection ends b
      in IS.size l == 1 && IS.size r == 1 && l /= r

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
sameStep (SelectRepeatedLink a) (SelectRepeatedLink b) = a == b
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
  , indexedRepeatedLinks :: ~(V.Vector RepeatedLinks)
  , indexedBoundary :: IS.IntSet
  }

indexHost :: (Eq l) => V.Vector (Signature l) -> Graph s l -> HostIndex s l
indexHost signatures (Graph ns ins outs bs) =
  HostIndex (V.fromList ns) boxes ids candidates incidence neighbours repeatedLinks (IS.fromList (ins ++ outs))
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
    boxes = V.fromList bs
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
    repeatedLinks = V.map (indexRepeatedLinks boxes neighbours . snd) candidates

-- Most binary connectors, including Hadamards in a ZX diagram, have a
-- unique neighbouring box at each wire. At a shared wire we index by one
-- endpoint instead of enumerating the cross product of neighbouring boxes.
data RepeatedLinks = RepeatedLinks
  { linkPairs :: IM.IntMap (Int, Int)
  , linksByPair :: M.Map (Int, Int) [Int]
  , sharedLinks :: IM.IntMap Int
  , linksByWire :: IM.IntMap [Int]
  , boxesAtSharedLinks :: IS.IntSet
  }

indexRepeatedLinks :: V.Vector (Box l Int) -> V.Vector (Int, [Int]) -> [Int] -> RepeatedLinks
indexRepeatedLinks boxes neighbours candidates = RepeatedLinks pairs byPair shared byWire nearby
  where
    (pairs, byPair, shared) = foldl' classify (IM.empty, M.empty, IM.empty) candidates
    byWire = IM.fromListWith (++) [(n, [i]) | (i, n) <- IM.toList shared]
    nearby = IS.fromList [i | n <- IM.keys byWire, i <- snd (neighbours V.! n)]
    classify state@(!known, !grouped, !unknown) i = case map snd (portsOf (boxes V.! i)) of
      [n, m]
        | n /= m -> case (adjacent i n, adjacent i m) of
            ([], _) -> state
            (_, []) -> state
            ([a], [b])
              | a /= b ->
                  let pair = (min a b, max a b)
                  in (IM.insert i pair known, M.insertWith (++) pair [i] grouped, unknown)
            ([_], [_]) -> state
            _ ->
              let endpoint = if fst (neighbours V.! n) <= fst (neighbours V.! m) then n else m
              in (known, grouped, IM.insert i endpoint unknown)
      _ -> state
    adjacent i n = filter (/= i) (snd (neighbours V.! n))

repeatedLinkCandidates :: HostIndex s l -> Int -> Int -> [Int]
repeatedLinkCandidates host sig first = case IM.lookup first (linkPairs links) of
  Just pair@(a, b) ->
    M.findWithDefault [] pair (linksByPair links)
      ++ IS.toList
        ( IS.fromList
            [ i
            | box <- [a, b]
            , IS.member box (boxesAtSharedLinks links)
            , n <- wires box
            , i <- IM.findWithDefault [] n (linksByWire links)
            ]
        )
  Nothing -> case IM.lookup first (sharedLinks links) of
    Just n ->
      IS.toList
        ( IS.fromList
            [ i
            | box <- neighbours n
            , box /= first
            , wire <- wires box
            , i <- neighbours wire
            , IS.member sig (indexedSignatures host V.! i)
            ]
        )
    Nothing -> []
  where
    links = indexedRepeatedLinks host V.! sig
    wires i = map snd (portsOf (indexedBoxes host V.! i))
    neighbours n = snd (indexedNeighbours host V.! n)

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
runStep host (SelectRepeatedLink sig) (m, range, order, used, captures) = case order of
  first : _ ->
    [ (m, range, i : order, IS.insert i used, captures)
    | i <- repeatedLinkCandidates host sig first
    , IS.notMember i used
    ]
  [] -> error "runStep: repeated link selection without a first box"
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

compiledMatches :: (Eq l, DecidableIso s) => CompiledRules key s l -> Graph s l -> [(Int, Prepared s l)]
compiledMatches = compiledMatchesAvoiding IS.empty

-- Protected nodes may occur inside captured sequences, but may not be
-- selected by a numbered pattern port (including an explicit interface).
compiledMatchesAvoiding
  :: (Eq l, DecidableIso s) => IS.IntSet -> CompiledRules key s l -> Graph s l -> [(Int, Prepared s l)]
compiledMatchesAvoiding protected rules = map (fmap fst) . compiledMatchesWith False protected rules

compiledHasPortMaps :: CompiledRules key s l -> Bool
compiledHasPortMaps (CompiledRules rules _ _ _) = V.any (hasMaps . snd) rules
  where
    hasMaps (PortRule _ MappedPorts{}) = True
    hasMaps (SortRule _ rule) = hasMaps rule
    hasMaps _ = False

compiledMatchesWithMaps
  :: (Eq l, DecidableIso s)
  => IS.IntSet -> CompiledRules key s l -> Graph s l -> [(Int, (Prepared s l, [(Int, Box l CaptureEnd)]))]
compiledMatchesWithMaps = compiledMatchesWith True

compiledMatchesWith
  :: (Eq l, DecidableIso s)
  => Bool
  -> IS.IntSet
  -> CompiledRules key s l
  -> Graph s l
  -> [(Int, (Prepared s l, [(Int, Box l CaptureEnd)]))]
compiledMatchesWith allowMaps protected (CompiledRules rules signatures net reducing) g =
  [ (i, prepared)
  | (i, _, _, prepared) <-
      sortOn
        (\(i, order, m, _) -> (i, order, IM.elems m))
        (walk net (IM.empty, IS.empty, [], IS.empty, M.empty))
  ]
  where
    host = indexHost signatures g
    walk (Net terminals branches) state@(registers, range, order, used, captures) =
      [ (i, originalOrder, mapping, prepared)
      | IS.disjoint protected range
      , Terminal i originalNodes boxRegisters <- terminals
      , let mapping = IM.map (registers IM.!) originalNodes
            (_, r) = rules V.! i
            originalOrder = map (boxImages V.!) boxRegisters
      , prepared@((lhs, Graph _ _ _ replacement, (nodes, selected)), _) <-
          prepareMatch allowMaps protected host r mapping used captures originalOrder
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
  => Bool
  -> IS.IntSet
  -> HostIndex s l
  -> Rule s l
  -> IM.IntMap Int
  -> IS.IntSet
  -> M.Map String [Int]
  -> [Int]
  -> [(Prepared s l, [(Int, Box l CaptureEnd)])]
prepareMatch _ _ host (Rule lhs instantiate) mapping used _ order = maybeToList $ do
  rhs <- instantiate [label (indexedBoxes host V.! i) | i <- order]
  pure ((lhs, rhs, (mapping, used)), [])
prepareMatch allowMaps protected host (PortRule (PortGraph ns interface _) replacement) mapping used captures order = maybeToList $ do
  (PortGraph rs rightInterface rightBoxes, mappings) <-
    instantiatePorts protected replacement captures (map label selected)
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
      port (Capture name) =
        case M.lookup name mappedPorts of
          Just nodes' -> Just nodes'
          Nothing -> map (rightIndices IM.!) <$> M.lookup name captures
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
      assignments = [(name, n, box) | (name, box) <- mappings, n <- captures M.! name]
      assign next (name, n, box)
        | IS.member n protected = (next, (name, rightIndices IM.! n, Left (n, box)))
        | otherwise =
            let attached Outer = rightIndices IM.! n
                attached Inner = next
            in (next + 1, (name, next, Right (indexedSorts host V.! n, fmap attached box)))
      (_, mapped) = mapAccumL assign (length rightSorts) assignments
      mappedPorts = fmap reverse (M.fromListWith (++) [(name, [n]) | (name, n, _) <- mapped])
      opaque = [entry | (_, _, Left entry) <- mapped]
      concrete = [entry | (_, _, Right entry) <- mapped]
      -- Moving a map onto the boundary is sound only when it wraps the
      -- whole sequence at its sole occurrence.
      unique n = sum (map fst (IM.elems (indexedIncidence host V.! n))) == 1
  unless (null opaque || (allowMaps && all (unique . fst) opaque)) Nothing
  boxes <- traverse (\(Box l is os) -> Box l <$> expand is <*> expand os) rightBoxes
  let right = Graph (rightSorts ++ map fst concrete) [rightIndices IM.! n | n <- kept] [] (boxes ++ map snd concrete)
  pure ((left, right, (IM.fromList (zip [0 ..] nodes), used)), opaque)
  where
    selected = [indexedBoxes host V.! i | i <- order]
prepareMatch _ _ host (SubgraphRule lhs rhs) mapping used _ _ =
  map (,[]) (prepareSubgraphs host lhs rhs mapping used)
prepareMatch _ _ host (SortRule instantiate (SubgraphRule lhs (Graph rs ri ro rb))) mapping used _ _ = do
  let Graph ls _ _ _ = lhs
      actual = [indexedSorts host V.! (mapping IM.! n) | n <- [0 .. length ls - 1]]
  sorts <- maybeToList (instantiate ls actual rs)
  if length sorts == length rs
    then map (,[]) (prepareSubgraphs host lhs (Graph sorts ri ro rb) mapping used)
    else []
prepareMatch allowMaps protected host (SortRule instantiate r) mapping used captures order = do
  ((Graph ls li lo lb, Graph rs ri ro rb, match@(images, _)), maps) <-
    prepareMatch allowMaps protected host r mapping used captures order
  maybeToList $ do
    let PortGraph patternSorts _ _ = rulePattern r
        actual = [indexedSorts host V.! (mapping IM.! n) | n <- [0 .. length patternSorts - 1]]
        leftSorts = [indexedSorts host V.! (images IM.! n) | n <- [0 .. length ls - 1]]
    rightSorts <- instantiate patternSorts actual rs
    unless (length rightSorts == length rs) Nothing
    unless (length li + length lo == length ri + length ro) Nothing
    unless (and [sameSort (leftSorts !! l) (rightSorts !! r') | (l, r') <- zip (li ++ lo) (ri ++ ro)]) Nothing
    pure ((Graph leftSorts li lo lb, Graph rightSorts ri ro rb, match), maps)

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
