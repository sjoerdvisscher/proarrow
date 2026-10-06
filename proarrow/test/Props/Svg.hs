{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The SVG diagrams mean what the Dot diagrams they carry mean, so their laws are checked with
-- Dot's equality. Drawing is checked only by rendering every law, with the default options and
-- with every option switched.
module Props.Svg where

import Control.Monad (forM_, replicateM)
import Data.List qualified as List
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (Monoid, elem, id, mappend, mempty, (.))

import Proarrow.Category.Monoidal (Monoidal, SymMonoidal, SymMonoidalStructures, withOb2)
import Proarrow.Category.Monoidal.Closed (ClosedStructures)
import Proarrow.Category.Monoidal.CompactClosed (CompactClosedStructures)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscardStructures)
import Proarrow.Category.Monoidal.Dialogue (DialogueStructures)
import Proarrow.Category.Monoidal.Hypergraph (FrobeniusStructures)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomousStructures)
import Proarrow.Category.Monoidal.Strength (TracedStructures)
import Proarrow.Category.Monoidal.Strictified (IsList (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), UN)
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid (..), Monoid (..), Supplies)
import Proarrow.Tools.Diagrams.Svg
  ( Diagram (..)
  , KnownWire
  , Options (..)
  , SVG (..)
  , Svg (..)
  , W (..)
  , bends
  , defaultOptions
  , hideUnits
  , kindsIn
  , kindsOut
  , lawSvgsWith
  , node
  , render
  , renderWith
  , slide
  , wires
  , withIsListErase
  )
import Proarrow.Tools.SMC.Examples (combineDualT, hadamardT, loopCC, matMulT, rotT, snakeT, swapT, traceIdxT)

import Proarrow.Testing
  ( Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , check
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Props.Dot (boxes)

test :: TestTree
test =
  testGroup
    "Svg"
    [ testCategory @SVG
    , testMonoidal_ @SVG
    , testSymMonoidal_ @SVG
    , testCopyDiscard_ @SVG
    , testMonoid_ @(S '[Wire "A"])
    , testMonoid_ @(S '[Wire "A", Co "B"])
    , testComonoid_ @(S '[Wire "A", I, Co "B"])
    , testHypergraph @SVG (\ @a @b r -> withOb2 @SVG @a @b r)
    , testClosed_ @SVG
    , testDialogue_ @SVG
    , testStarAutonomous_ @SVG
    , testIsoMix_ @SVG
    , testCompactClosed_ @SVG
    , testTraced_ @SVG
    , testProperty "every law draws as an equation" $ do
        let everything =
              Options
                { explicitIdentities = True
                , explicitCoherence = True
                , explicitSwaps = True
                , fixedSpiders = False
                , bendSpiders = True
                , slidePoints = True
                }
            structures :: [[(String, String)]]
            structures =
              [ drawn
              | o <- [defaultOptions, everything, defaultOptions{bendSpiders = True, slidePoints = True}]
              , drawn <-
                  [ lawSvgsWith @'[CategoryOf] o
                  , lawSvgsWith @'[Monoidal] o
                  , lawSvgsWith @SymMonoidalStructures o
                  , lawSvgsWith @ClosedStructures o
                  , lawSvgsWith @DialogueStructures o
                  , lawSvgsWith @StarAutonomousStructures o
                  , lawSvgsWith @CompactClosedStructures o
                  , lawSvgsWith @'[Monoidal, Supplies Monoid] o
                  , lawSvgsWith @'[Monoidal, Supplies Comonoid] o
                  , lawSvgsWith @'[Monoidal, SymMonoidal, Supplies CommutativeMonoid] o
                  , lawSvgsWith @'[Monoidal, SymMonoidal, Supplies CocommutativeComonoid] o
                  , lawSvgsWith @FrobeniusStructures o
                  , lawSvgsWith @TracedStructures o
                  , lawSvgsWith @CopyDiscardStructures o
                  ]
              ]
        forM_ structures \drawn -> do
          check "a structure drew no laws" (not (null drawn))
          -- reads every character of the drawing, so its layout is computed in full
          forM_ drawn \(name, d) ->
            check (name ++ " drew malformed markup") (count '<' d > 0 && count '<' d == count '>' d)
    , testProperty "with bent spiders, the trace in index notation draws no points" $ do
        let t = traceIdxT @(S '[Wire "A"]) (node "f")
        check "the default draws no points" (points (render t) == 4)
        check "points are left" (points (renderWith defaultOptions{bendSpiders = True} t) == 0)
    , testProperty "slid and bent, matrix multiplication in index notation draws no points" $ do
        let m = matMulT @(S '[Wire "A"]) @(S '[Wire "B"]) @(S '[Wire "A"]) (node "f") (node "g")
        check "the default draws no points" (points (render m) == 8)
        check "points are left" (points (renderWith defaultOptions{bendSpiders = True, slidePoints = True} m) == 0)
    , testProperty "sliding points and bending spiders keep every stack's wires matching, with or without unit wires" $
        forM_
          @[]
          [ tree (traceIdxT @(S '[Wire "A"]) (node "f"))
          , tree (hadamardT @(S '[Wire "A"]) @(S '[Wire "B"]) (node "f") (node "g"))
          , tree (matMulT @(S '[Wire "A"]) @(S '[Wire "B"]) @(S '[Wire "A"]) (node "f") (node "g"))
          , tree (loopCC @(S '[Wire "A"]) @(S '[Wire "B"]) @(S '[Wire "A"]) (node "h"))
          , tree (snakeT @(S '[Wire "A"]))
          , tree (combineDualT @(S '[Wire "A"]) @(S '[Wire "B"]))
          , tree (swapT @(S '[Wire "A"]) @(S '[Wire "B"]))
          , tree (rotT @(S '[Wire "A"]) @(S '[Wire "B"]) @(S '[Wire "A"]))
          ]
          \d -> do
            -- with the unit wires shown, as with explicit coherence, and with them hidden
            forM_ @[] [d, hideUnits d] \h -> do
              check "a stack's wires do not match before" (matching h)
              forM_ @[] [slide h, bends h, bends (slide h)] \d' -> do
                check "a stack's wires do not match" (matching d')
                check "the boundary changed" (kindsIn d' == kindsIn h && kindsOut d' == kindsOut h)
    , testProperty "with bent spiders, a merge and a discard on two wires draw a cap, and a unit and a copy a cup" $
        forM_ @[] [defaultOptions{bendSpiders = True}, defaultOptions{bendSpiders = True, slidePoints = True}] \o -> do
          check "the cap has points" (points (renderWith o (counit @(S '[Wire "A", Wire "B"]) . mappend)) == 0)
          check "the cup has points" (points (renderWith o (comult . mempty @(S '[Wire "A", Wire "B"]))) == 0)
    , testProperty "with bent spiders, the entrywise product keeps only its copy points" $ do
        let h = hadamardT @(S '[Wire "A"]) @(S '[Wire "B"]) (node "f") (node "g")
        check "the default draws other points" (points (render h) == 8)
        check "other points are left" (points (renderWith defaultOptions{bendSpiders = True} h) == 2)
    ]
  where
    -- every point is drawn as one circle
    points = length . filter ("<circle" `List.isPrefixOf`) . List.tails
    tree :: Svg a b -> Diagram
    tree (Svg _ d) = d
    -- the wires coming out of every step of a stack are the ones going into the next
    matching = \case
      Seq a b -> kindsOut a == kindsIn b && matching a && matching b
      Beside a b -> matching a && matching b
      Trace _ d -> matching d
      _ -> True

-- | A wire of the palette objects are drawn from.
data SomeWire where
  SomeWire :: forall (w :: W). (KnownWire w) => SomeWire

-- | Up to two wires, each a plain wire, a dual wire or the unit wire, so that the laws are checked
-- where the meaning leaves wires out or forgets that they are dual.
instance Testable SVG where
  genSome = do
    num <- elem [0 .. 2]
    ws <- replicateM num (elem [SomeWire @(Wire "A"), SomeWire @(Wire "B"), SomeWire @(Co "A"), SomeWire @I])
    pure (foldWires ws)
  showOb @ws = List.intercalate "," $ map fst $ wires @(UN S ws)

foldWires :: [SomeWire] -> Some SVG
foldWires [] = Some @(S '[])
foldWires [SomeWire @w] = Some @(S '[w])
foldWires (SomeWire @w : rest) = case foldWires rest of
  Some @(S ws) -> withIsList2 @'[w] @ws (Some @(S (w ': ws)))

instance (Ob a, Ob b) => TestingEqShow (Svg a b) where
  eqP (Svg @as @bs l _) (Svg r _) = withIsListErase @as $ withIsListErase @bs $ eqP l r

-- | Boxes through the library's own operations, as for Dot.
instance (Ob a, Ob b) => TestableType (Svg a b) where
  gen = GenNonEmpty (boxes @a @b \ @x @y -> node @(UN S x) @(UN S y))

instance TestableProfunctor Svg

-- | How often a character occurs in a string.
count :: Char -> String -> Int
count c = length . filter (== c)
