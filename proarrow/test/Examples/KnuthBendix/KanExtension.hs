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
module Examples.KnuthBendix.KanExtension
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
import Data.Maybe (fromMaybe, isNothing)
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding ((.))

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), Rewrite (..), emb, path)
import Proarrow.Core (CAT, Promonad (..))
import Proarrow.Object (SomeOb, SomeOf (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.KnuthBendix.NormalForms qualified as NF
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

objects :: [SomeOb Type]
objects = [Some @Root, Some @Line]

normalForms :: NF.NormalForms Action
normalForms = case NF.compile objects [NF.Generator StepRight, NF.Generator StepLeft, NF.Generator Reflect, NF.Generator Seed] completion of
  Just forms -> forms
  Nothing -> error "induced action normal-form compilation failed"

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
elements = fromMaybe (error "missing induced action endpoint") (NF.enumerate @Root @Line normalForms)

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
        expect "infinitely many induced elements" (Just NF.Infinite) (NF.cardinality @Root @Line normalForms)
        expect "infinitely many group elements" (Just NF.Infinite) (NF.cardinality @Line @Line normalForms)
        expect "no arrows back to the root" (Just (NF.Finite 0)) (NF.cardinality @Line @Root normalForms)
        expect
          "source-wide counts include finite and infinite hom-sets"
          (Just [(Some @Root, NF.Finite 1), (Some @Line, NF.Infinite)])
          (NF.cardinalitiesFrom @Root normalForms)
        expect
          "source-wide counts include unreachable targets"
          (Just [(Some @Root, NF.Finite 0), (Some @Line, NF.Infinite)])
          (NF.cardinalitiesFrom @Line normalForms)
        expect
          "target-wide counts include finite and empty hom-sets"
          (Just [(Some @Root, NF.Finite 1), (Some @Line, NF.Finite 0)])
          (NF.cardinalitiesTo @Root normalForms)
        expect
          "target-wide counts propagate infinity back to each source"
          (Just [(Some @Root, NF.Infinite), (Some @Line, NF.Infinite)])
          (NF.cardinalitiesTo @Line normalForms)
        expect "only the root identity" (Just ["id"]) (fmap (map show) (NF.enumerate @Root @Root normalForms))
        expect "no arrows back to the root" (Just []) (fmap (map show) (NF.enumerate @Line @Root normalForms))
        expect "no initial object" [] (NF.initialObjects normalForms)
        expect "no terminal object" [] (NF.terminalObjects normalForms)
        check
          "infinite hom-sets can leave epi–mono factorisation undecided"
          (isNothing (NF.epiMonoFactorization normalForms (PCons Seed PNil)))
        expect
          "a product can use only finite hom-sets in an infinite presentation"
          (Just 1)
          (length <$> NF.binaryProducts @Root @Root normalForms)
        check
          "infinite product and coproduct candidates are undecided"
          (isNothing (NF.binaryProducts @Line @Line normalForms) && isNothing (NF.binaryCoproducts @Line @Line normalForms))
        let discrete = KB.complete (KB.Limits 1 1) [] :: KB.Completion Action
        check
          "a generator with an undeclared endpoint is rejected"
          (isNothing (NF.compile [Some @Line] [NF.Generator Seed] discrete))
        isolated <-
          maybe (testFailed "failed to compile the isolated object") pure (NF.compile [Some @Root, Some @Root] [] discrete)
        expect "the declared isolated object has an identity" (Just (NF.Finite 1)) (NF.cardinality @Root @Root isolated)
        expect "duplicate objects are removed" [Some @Root] (NF.initialObjects isolated)
        expect "undeclared endpoint has no cardinality" Nothing (NF.cardinality @Root @Line isolated)
        check
          "undeclared endpoint cannot be enumerated or plotted"
          (isNothing (NF.enumerate @Root @Line isolated) && isNothing (NF.renderDot @Root @Line isolated))
        expect "cancellation requires declared endpoints" Nothing (NF.isEpi isolated (PNil :: GroupWord))
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
