-- | An infinite Set-valued left Kan extension with a finite rewrite system.
-- Induce the singleton action of H = <Reflect> along H -> D_infinity, where
-- the infinite dihedral group has a translation, its inverse and a reflection.
-- The right cosets gH are in bijection with the integers.
--
-- A fresh Root and Seed : Root -> Line encode the singleton, with the tag
-- equation Reflect . Seed = Seed. Normal forms are Seed, StepRight^n . Seed
-- and StepLeft^n . Seed for n > 0. Their integer interpretation is 0, n and -n,
-- respectively. Every integer has a representative, and the defining equations
-- preserve this interpretation, so distinct integers cannot be identified.
-- This establishes an infinite result, rather than just a large finite sample.
--
-- For any D_infinity-action and reflection-fixed point y, sending g . Seed
-- to g acting on y gives the unique equivariant map extending the singleton.
module Examples.KanExtension
  ( test
  , Action (..)
  , Element
  , inducedSystem
  , at
  , coordinate
  , elements
  , completedRules
  ) where

import Data.Kind (Type)
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((.))

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), Rewrite (..), emb, path)
import Proarrow.Core (CAT, Promonad (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.Laws (ProEquation ((:=:)))
import Proarrow.Tools.Laws qualified as Laws

data Root
data Line

type Action :: CAT Type
data Action a b where
  StepRight :: Action Line Line
  StepLeft :: Action Line Line
  Reflect :: Action Line Line
  Seed :: Action Root Line

deriving instance Show (Action a b)

instance EqGen Action where
  eqGen StepRight StepRight = Just Refl
  eqGen StepLeft StepLeft = Just Refl
  eqGen Reflect Reflect = Just Refl
  eqGen Seed Seed = Just Refl
  eqGen _ _ = Nothing

rank :: Action a b -> Int
rank StepRight = 0
rank StepLeft = 1
rank Reflect = 2
rank Seed = 3

type GroupWord = Paths (PTH Line :: PATHS Action) (PTH Line)
type Element = Paths (PTH Root :: PATHS Action) (PTH Line)

equations :: [KB.Equation Action]
equations =
  [ path StepRight StepLeft :=: path
  , path StepLeft StepRight :=: path
  , path Reflect Reflect :=: path
  , path Reflect StepRight :=: path StepLeft Reflect
  , path Reflect Seed :=: path Seed
  ]

completion :: KB.Completion Action
completion = KB.completeWithOrder rank (KB.Limits 100 2000) equations

inducedSystem :: KB.System Action
inducedSystem = case completion of
  KB.Complete system -> system
  KB.Incomplete reason _ _ -> error ("infinite induced action completion: " ++ show reason)

instance Rewrite Action where
  rewrite = KB.rewrite inducedSystem

-- Construct the representative of any integer without enumerating the set.
at :: Integer -> Element
at n = go (abs n) (if n < 0 then StepLeft else StepRight) (emb Seed)
  where
    go :: Integer -> Action Line Line -> Element -> Element
    go 0 _ p = p
    go k step p = go (k - 1) step (emb step . p)

-- Independent action on unbounded integers, also defined on raw tagged paths.
coordinate :: Element -> Integer
coordinate (PCons Seed _) = 0
coordinate (PCons StepRight more) = coordinate more + 1
coordinate (PCons StepLeft more) = coordinate more - 1
coordinate (PCons Reflect more) = negate (coordinate more)

-- A lazy enumeration: 0, 1, -1, 2, -2, ... . Consumers can take finite prefixes.
elements :: [Element]
elements = emb Seed : concat (zipWith (\r l -> [r, l]) positive negative)
  where
    positive = iterate (emb StepRight .) (emb StepRight . emb Seed)
    negative = iterate (emb StepLeft .) (emb StepLeft . emb Seed)

completedRules :: [String]
completedRules = [KB.withRule r (\l rhs -> show l ++ " -> " ++ show rhs) | r <- KB.rules inducedSystem]

-- Raw words exercise cancellation and reflection before interpreting the tag.
wordsUpTo :: Int -> [GroupWord]
wordsUpTo 0 = [PNil]
wordsUpTo n = PNil : concat [[PCons StepRight p, PCons StepLeft p, PCons Reflect p] | p <- wordsUpTo (n - 1)]

tagged :: GroupWord -> Element
tagged PNil = path Seed
tagged (PCons StepRight more) = PCons StepRight (tagged more)
tagged (PCons StepLeft more) = PCons StepLeft (tagged more)
tagged (PCons Reflect more) = PCons Reflect (tagged more)

test :: TestTree
test =
  testGroup
    "Infinite Kan extension"
    [ testProperty "a finite completion represents infinitely many cosets" $ do
        case completion of
          KB.Complete _ -> pure ()
          KB.Incomplete reason _ _ -> testFailed (show reason)
        check "all presentation equations hold" (all (\e -> Laws.withSides e (KB.equivalent inducedSystem)) equations)
        let prefix = take 41 elements
            expected = 0 : concat [[n, -n] | n <- [1 .. 20]]
        expect "lazy enumeration visits both directions" expected (map coordinate prefix)
        expect "distinct normal forms in the prefix" 41 (S.size (S.fromList (map show prefix)))
    , testProperty "raw tagged words normalise to their independent integer coordinates" $ do
        let raw = map tagged (wordsUpTo 7)
        check "incorrect integer representative" (all (\p -> KB.normalise inducedSystem p == at (coordinate p)) raw)
    , testProperty "further arrow actions work without enumerating the result" $ do
        let points = [-100, -17, -1, 0, 1, 17, 100]
        check "integer representatives preserve their coordinates" (all (\n -> coordinate (at n) == n) points)
        check "step right" (all (\n -> emb StepRight . at n == at (n + 1)) points)
        check "step left" (all (\n -> emb StepLeft . at n == at (n - 1)) points)
        check "reflection" (all (\n -> emb Reflect . at n == at (-n)) points)
    ]
