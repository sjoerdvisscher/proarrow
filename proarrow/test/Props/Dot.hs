{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Dot where

import Control.Monad (forM_, replicateM, when)
import Data.Containers.ListUtils (nubOrd)
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Type.Equality ((:~:) (..))
import Data.Void (absurd)
import GHC.TypeLits (Symbol, decideSymbol, symbolVal)
import Test.Falsify.Generator (Gen, elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude hiding (elem, fst, id, snd, (.))

import Proarrow.Category.Monoidal (Monoidal, SymMonoidalStructures, withOb2)
import Proarrow.Category.Monoidal.Closed (ClosedStructures)
import Proarrow.Category.Monoidal.CompactClosed (CompactClosedStructures)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomousStructures)
import Proarrow.Category.Monoidal.Strictified (IsList (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), UN)
import Proarrow.Tools.Diagrams.Dot
  ( DOT (..)
  , Dot (..)
  , DotData (..)
  , Fin (..)
  , NodeKind (..)
  , SymRefl (..)
  , Vec (..)
  , getData
  , lawDiagrams
  , len
  , names
  , node
  , nodeOf
  , portOf
  )

import Proarrow.Testing
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , genSomeDef
  , oneElem
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws

test :: TestTree
test =
  testGroup
    "Dot"
    [ testCategory @DOT
    , testMonoidal_ @DOT
    , testSymMonoidal_ @DOT
    , testCopyDiscard_ @DOT
    , testMonoid_ @(D '[])
    , testMonoid_ @(D '["A"])
    , testMonoid_ @(D '["A", "B"])
    , testCommutativeMonoid_ @(D '["A", "B"])
    , testComonoid_ @(D '["A", "B"])
    , testHypergraph @DOT (\r -> r) (\ @a @b r -> withOb2 @DOT @a @b r)
    , testClosed_ @DOT
    , testStarAutonomous_ @DOT
    , testCompactClosed_ @DOT
    , testProperty "every law draws as an equation" $ do
        let structures :: [[(String, String)]]
            structures =
              [ lawDiagrams @'[Monoidal]
              , lawDiagrams @SymMonoidalStructures
              , lawDiagrams @ClosedStructures
              , lawDiagrams @StarAutonomousStructures
              , lawDiagrams @CompactClosedStructures
              ]
        forM_ structures \drawn -> do
          when (null drawn) (testFailed "a structure drew no laws")
          forM_ drawn \(name, d) -> when (null d) (testFailed (name ++ " drew nothing"))
    ]

foldSome :: [Some Symbol] -> Some DOT
foldSome [] = Some @(D '[])
foldSome [Some @n] = Some @(D '[n])
foldSome (Some @n : Some @m : rest) = case foldSome (Some @m : rest) of
  Some @(D ns) -> withIsList2 @'[n] @ns (Some @(D (n ': ns)))

instance Testable Symbol where
  genSome = genSomeDef @'["A", "B", "C", "D", "E"]
  showOb @s = symbolVal (Proxy @s)

instance (Ob a, Ob b) => TestingEqShow (SymRefl a b)
instance (Ob a, Ob b) => TestableType (SymRefl a b) where
  gen = case decideSymbol (Proxy @a) (Proxy @b) of
    Right Refl -> oneElem SymRefl
    Left f -> GenEmpty \SymRefl -> absurd (f Refl)
instance TestableProfunctor SymRefl
instance Testable DOT where
  genSome = do
    num <- elem [0 .. 2]
    somes <- replicateM num (genSome @Symbol)
    pure $ foldSome somes
  showOb @ns = List.intercalate "," $ unVec $ names @(UN D ns)

-- | Two diagrams are equal when they mean the same relation ('meaning'), under a few different
-- meanings of the labelled nodes.
instance (Ob a, Ob b) => TestingEqShow (Dot a b) where
  eqP l r = let dl = getData l; dr = getData r in pure (all (\seed -> meaning seed dl == meaning seed dr) ([1, 2, 3] :: [Int]))

-- | A diagram through the library's own operations, so that its nodes are numbered as the other
-- arrows' are: one labelled node from the inputs to the outputs, or two stacked through a random
-- boundary in between.
instance (Ob a, Ob b) => TestableType (Dot a b) where
  gen = GenNonEmpty do
    stacked <- elem [False, True]
    if stacked
      then do
        Some @m <- genSome @DOT
        (.) <$> labelled @m @b <*> labelled @a @m
      else labelled @a @b

labelled :: forall a b. (Ob a, Ob b) => Gen (Dot a b)
labelled = do
  l <- elem ["f", "g", "h"]
  pure (node @(UN D a) @(UN D b) l)

-- * What a diagram means

-- | A wire of a diagram: an input, an output, or an edge between two nodes.
data Wire = InWire Int | OutWire Int | EdgeWire Int
  deriving (Eq, Ord, Show)

-- | Which way a wire runs at the node it is attached to.
data End = Into | OutOf
  deriving (Eq, Ord, Show)

-- | The relation a diagram means, every wire carrying one bit: the set of pairs of input and
-- output bits it relates. A 'Spider' means that all its wires agree, a 'Crossing' swaps its two
-- wires, and a 'Box' is a free generator, which the seed gives a pseudo-random meaning that
-- depends on its label and on the wires it has, but not on their order.
meaning
  :: forall (as :: [Symbol]) (bs :: [Symbol]). (IsList as, IsList bs) => Int -> DotData as bs -> Set ([Bool], [Bool])
meaning seed (DotData is os es ns) =
  Set.fromList [(map (bitOf . InWire) inIxs, map (bitOf . OutWire) outIxs) | bitOf <- joined]
  where
    inIxs = [0 .. len @as - 1]
    outIxs = [0 .. len @bs - 1]
    inNames = unVec (names @as)
    outNames = unVec (names @bs)
    -- every attachment of a wire to a node, and every wire going straight through
    attached =
      [(nodeOf p, (Into, portOf p, inNames !! i, InWire i)) | (i, Right p) <- zip [0 ..] (unVec is)]
        ++ [(nodeOf p, (OutOf, portOf p, outNames !! j, OutWire j)) | (j, Right p) <- zip [0 ..] (unVec os)]
        ++ concat
          [ [(nodeOf p1, (OutOf, portOf p1, l, EdgeWire k)), (nodeOf p2, (Into, portOf p2, l, EdgeWire k))]
          | (k, (p1, l, p2)) <- zip [0 ..] es
          ]
    through = [(InWire i, OutWire (unFin j)) | (i, Left j) <- zip [0 ..] (unVec is)]
    factors =
      [nodeFactor seed nd [w | (m, w) <- attached, m == n] | (n, nd) <- zip [0 ..] ns]
        ++ [([x, y], [Map.fromList [(x, v), (y, v)] | v <- [False, True]]) | (x, y) <- through]
    boundary = Set.fromList (map InWire inIxs ++ map OutWire outIxs)
    -- every boundary wire is on a node or goes straight through, so each row has them all
    joined = [(t Map.!) | t <- joinAll boundary factors]

-- | A node as a table over its wires: every assignment of bits to them that it allows.
nodeFactor :: Int -> (NodeKind, String) -> [(End, String, String, Wire)] -> ([Wire], [Map Wire Bool])
nodeFactor seed (kind, opts) ws = (wires, filter holds (assignments wires))
  where
    wires = nubOrd [w | (_, _, _, w) <- ws]
    bits t = [(e, port, l, t Map.! w) | (e, port, l, w) <- ws]
    holds t = case kind of
      Crossing -> crossing (bits t)
      Spider -> allSame [b | (_, _, _, b) <- bits t]
      Box -> even (hashFrom nodeHash (show (List.sort (bits t))))
    crossing bs = lookupBit Into ":nw" bs == lookupBit OutOf ":se" bs && lookupBit Into ":ne" bs == lookupBit OutOf ":sw" bs
    lookupBit e port bs = [b | (e', port', _, b) <- bs, e' == e, port' == port]
    allSame bs = and (zipWith (==) bs (drop 1 bs))
    -- the node's own part of the hash, once rather than for every assignment
    nodeHash = hashFrom 7 (show (seed, opts))
    hashFrom = foldl (\h c -> (h * 31 + fromEnum c) `mod` 1000003)

assignments :: [Wire] -> [Map Wire Bool]
assignments = foldr (\w ts -> [Map.insert w v t | t <- ts, v <- [False, True]]) [Map.empty]

-- | The natural join of the tables, forgetting a wire once no table left mentions it and it is not
-- on the boundary. Tables are taken in order of how many wires they share with the join so far.
joinAll :: Set Wire -> [([Wire], [Map Wire Bool])] -> [Map Wire Bool]
joinAll boundary = go Set.empty [Map.empty]
  where
    go _ ts [] = ts
    go seen ts fs =
      let ((ws, rows), rest) = List.maximumBy (comparing (\(f, _) -> score f)) (picks fs)
          ts' = [Map.union t r | t <- ts, r <- rows, and (Map.intersectionWith (==) t r)]
          live = boundary `Set.union` Set.fromList (concat [ws' | (ws', _) <- rest])
      in go (seen `Set.union` Set.fromList ws) (Set.toList (Set.fromList [Map.restrictKeys t live | t <- ts'])) rest
      where
        score (ws, _) = (length (filter (`Set.member` seen) ws), negate (length ws))
    picks xs = [(x, before ++ after) | (before, x : after) <- zip (List.inits xs) (List.tails xs)]

instance TestableProfunctor Dot
