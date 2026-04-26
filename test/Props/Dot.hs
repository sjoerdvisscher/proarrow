{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Props.Dot where

import Control.Monad (replicateM)
import Data.List (findIndices, intercalate)
import Data.List.NonEmpty (fromList)
import Data.Proxy (Proxy (..))
import Data.Traversable (for)
import Data.Type.Equality ((:~:) (..), TestEquality (testEquality))
import Data.Void (absurd)
import GHC.TypeLits (Symbol, decideSymbol, symbolVal, pattern SSymbol)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Prelude hiding (elem, fst, id, snd, (.))

import Proarrow.Category.Monoidal.Strictified (IsList (..), SList (..))
import Proarrow.Core (CategoryOf (..), Promonad (..), UN)
import Proarrow.Tools.Diagrams.Dot
  ( DOT (..)
  , Dot (..)
  , DotData (..)
  , Fin (..)
  , SymRefl (..)
  , Vec (..)
  , ixs
  , names
  , node
  , (!)
  )

import Props
import Testable
  ( GenTotal (..)
  , Some (..)
  , Testable (..)
  , TestableType (..)
  , TestingEqShow
  , genSomeDef
  , one
  , pattern GenNonEmpty
  )

test :: TestTree
test =
  testGroup
    "Dot"
    [ propCategory @DOT
    , propMonoidal_ @DOT
    , propSymMonoidal_ @DOT
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
    Right Refl -> one SymRefl
    Left f -> GenEmpty \SymRefl -> absurd (f Refl)
instance Testable DOT where
  genSome = do
    num <- elem [0 .. 5]
    somes <- replicateM num (genSome @Symbol)
    pure $ foldSome somes
  showOb @ns = intercalate "," $ unVec $ names @(UN D ns)
  eqOb @(D s) @(D t) =
    case (sList @s, sList @t) of
      (SNil, SNil) -> Just Refl
      (SSing @a, SSing @b) -> (\Refl -> Refl) <$> testEquality (SSymbol @a) (SSymbol @b)
      (SCons @a @as, SCons @b @bs) -> (\Refl Refl -> Refl) <$> testEquality (SSymbol @a) (SSymbol @b) <*> eqOb @DOT @(D as) @(D bs)
      _ -> Nothing

instance (Ob a, Ob b) => TestingEqShow (Dot a b)
instance (Ob a, Ob b) => TestableType (Dot a b) where
  gen = GenNonEmpty $ do
    let iIxs = ixs @(UN D a)
        oIxs = ixs @(UN D b)
        iNms = names @(UN D a)
        oNms = names @(UN D b)
    nodeCount <- if any (`notElem` iNms) oNms || any (`notElem` oNms) iNms then elem [1 .. 5] else elem [0 .. 5]
    nodeOpts <- replicateM nodeCount $ do
      label <- elem ["f", "g", "h"]
      pure $ "label=" ++ label
    edgeCount <- elem [0 .. 10]
    edges <- replicateM edgeCount $ do
      i <- elem [0 .. 5 :: Int]
      o <- elem [0 .. 5 :: Int]
      label <- elem ["A", "B", "C", "D", "E"]
      pure (show i, label, show o)
    inputs <- for iIxs $ \i -> do
      let nm = iNms ! i
      let pos = findIndices (== nm) (unVec oNms)
      let lst = (Right . show <$> [0 .. nodeCount - 1]) ++ (Left . Fin <$> pos)
      if length lst == 0
        then error $ "input: " ++ nm ++ " outputs: " ++ show oNms ++ " nodeCount: " ++ show nodeCount
        else elem . fromList $ lst
    outputs <- for oIxs $ \o -> do
      case findIndices (== Left o) (unVec inputs) of
        [i] -> pure $ Left (Fin i)
        [] ->
          if nodeCount == 0
            then pure $ Right "error" -- No input picked this output, bail out
            else Right . show <$> elem [0 .. nodeCount - 1]
        _ -> pure $ Right "error" -- Multiple inputs picked this output, bail out
    if any (== Right "error") outputs
      then pure (node "g")
      else pure $ Dot \n -> (n + nodeCount, DotData{inputs, outputs, edges, nodeOpts})
