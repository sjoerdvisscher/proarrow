{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The SVG diagrams mean what the Dot diagrams they carry mean, so their laws are checked with
-- Dot's equality. Drawing is checked only by rendering every law, with the default options and
-- with every option switched.
module Props.Svg where

import Control.Monad (forM_, replicateM, when)
import Data.List qualified as List
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testFailed, testProperty)
import Prelude hiding (Monoid, elem, id, (.))

import Proarrow.Category.Monoidal (Monoidal, SymMonoidal, SymMonoidalStructures, withOb2)
import Proarrow.Category.Monoidal.Closed (ClosedStructures)
import Proarrow.Category.Monoidal.CompactClosed (CompactClosedStructures)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscardStructures)
import Proarrow.Category.Monoidal.Hypergraph (FrobeniusStructures)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomousStructures)
import Proarrow.Category.Monoidal.Strength (TracedStructures)
import Proarrow.Category.Monoidal.Strictified (IsList (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), UN)
import Proarrow.Monoid (CocommutativeComonoid, CommutativeMonoid, Comonoid, Monoid, Supplies)
import Proarrow.Tools.Diagrams.Svg
  ( KnownWire
  , Options (..)
  , SVG (..)
  , Svg (..)
  , W (..)
  , defaultOptions
  , lawSvgsWith
  , node
  , wires
  , withIsListErase
  )

import Proarrow.Testing
  ( Some (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
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
    , testStarAutonomous_ @SVG
    , testCompactClosed_ @SVG
    , testTraced_ @SVG
    , testProperty "every law draws as an equation" $ do
        let everything = Options{explicitIdentities = True, explicitCoherence = True, explicitSwaps = True, fixedSpiders = False}
            structures :: [[(String, String)]]
            structures =
              [ drawn
              | o <- [defaultOptions, everything]
              , drawn <-
                  [ lawSvgsWith @'[CategoryOf] o
                  , lawSvgsWith @'[Monoidal] o
                  , lawSvgsWith @SymMonoidalStructures o
                  , lawSvgsWith @ClosedStructures o
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
          when (null drawn) (testFailed "a structure drew no laws")
          -- reads every character of the drawing, so its layout is computed in full
          forM_ drawn \(name, d) ->
            when (count '<' d == 0 || count '<' d /= count '>' d) (testFailed (name ++ " drew malformed markup"))
    ]

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
