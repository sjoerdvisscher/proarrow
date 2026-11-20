-- | Completion for a codec with two object colours. Decoding an encoding is an
-- identity; encoding a decoding canonicalises the representation. Completion
-- derives idempotence and the two ways to remove redundant canonicalisation.
module Examples.KnuthBendix (test, Codec (..), codecSystem, completedRules, redundantRules) where

import Data.Kind (Type)
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))
import Prelude qualified as P

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), Rewrite (..), emb, path)
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.Laws (ProEquation ((:=:)))
import Proarrow.Tools.Laws qualified as Laws

type Codec :: CAT Type
data Codec a b where
  Encode :: Codec Bool Int
  Decode :: Codec Int Bool
  Canonicalise :: Codec Int Int

deriving instance Show (Codec a b)

instance EqGen Codec where
  eqGen Encode Encode = Just Refl
  eqGen Decode Decode = Just Refl
  eqGen Canonicalise Canonicalise = Just Refl
  eqGen _ _ = Nothing

-- Raw paths keep presentation building independent of Rewrite below.
equations :: [KB.Equation Codec]
equations =
  [ path Decode Encode :=: path
  , path Encode Decode :=: path Canonicalise
  ]

completion :: KB.Completion Codec
completion = KB.complete (KB.Limits 20 200) equations

codecSystem :: KB.System Codec
codecSystem = case completion of
  KB.Complete system -> system
  KB.Incomplete reason _ _ -> error ("codec completion: " ++ show reason)

completedRules :: [String]
completedRules = renderRules codecSystem

renderRules :: KB.System Codec -> [String]
renderRules system = [KB.withRule r (\l rhs -> show l ++ " -> " ++ show rhs) | r <- KB.rules system]

-- Earlier hand-written optimisations become redundant once the two codec
-- equations are known. Completion should leave the same five basic rules.
redundantPresentation :: [KB.Equation Codec]
redundantPresentation =
  [ path Decode Canonicalise Canonicalise :=: path Decode
  , path Encode Decode Canonicalise :=: path Canonicalise Canonicalise
  ]
    ++ equations

redundantCompletion :: KB.Completion Codec
redundantCompletion = KB.complete (KB.Limits 20 200) redundantPresentation

redundantRules :: Either String [String]
redundantRules = case redundantCompletion of
  KB.Complete system -> Right (renderRules system)
  KB.Incomplete reason _ _ -> Left (show reason)

-- Successful completion compiles the matcher used by ordinary composition.
instance Rewrite Codec where
  rewrite = KB.rewrite codecSystem

type Value = PTH Bool :: PATHS Codec
type Representation = PTH Int :: PATHS Codec

interpret :: Paths (PTH a :: PATHS Codec) (PTH b) -> a -> b
interpret PNil = P.id
interpret (PCons p more) = step p P.. interpret more
  where
    step :: Codec x y -> x -> y
    step Encode = fromEnum
    step Decode = odd
    step Canonicalise = (`mod` 2)

-- Enumerate raw paths independently of the normalising composition instance.
type Sort :: Type -> Type
data Sort a where
  ValueSort :: Sort Bool
  RepresentationSort :: Sort Int

paths :: forall a b. Int -> Sort a -> Sort b -> [Paths (PTH a :: PATHS Codec) (PTH b)]
paths n a b = identities ++ if n <= 0 then [] else steps
  where
    identities :: [Paths (PTH a :: PATHS Codec) (PTH b)]
    identities = case (a, b) of
      (ValueSort, ValueSort) -> [PNil]
      (RepresentationSort, RepresentationSort) -> [PNil]
      _ -> []
    steps :: [Paths (PTH a :: PATHS Codec) (PTH b)]
    steps = case b of
      ValueSort -> [PCons Decode p | p <- paths (n - 1) a RepresentationSort]
      RepresentationSort ->
        [PCons Encode p | p <- paths (n - 1) a ValueSort]
          ++ [PCons Canonicalise p | p <- paths (n - 1) a RepresentationSort]

preserves :: (Eq b) => [a] -> [Paths (PTH a :: PATHS Codec) (PTH b)] -> Bool
preserves inputs = all $ \p ->
  let normal = KB.normalise codecSystem p
  in all (\x -> interpret p x == interpret normal x) inputs

test :: TestTree
test =
  testGroup
    "Coloured KB codec"
    [ testProperty "completion derives three useful codec equations" $ do
        case completion of
          KB.Incomplete reason _ _ -> testFailed (show reason)
          KB.Complete _ -> pure ()
        expect "two input equations and three derived rules" 5 (length completedRules)
        check "idempotence was discovered" ("Canonicalise . Canonicalise -> Canonicalise" `elem` completedRules)
        check "decode removes canonicalisation" ("Decode . Canonicalise -> Decode" `elem` completedRules)
        check "encoded values are canonical" ("Canonicalise . Encode -> Encode" `elem` completedRules)
    , testProperty "earlier codec shortcuts disappear after interreduction" $ do
        actual <- either testFailed pure redundantRules
        expect "five active rules" 5 (length actual)
        expect "same five rules" (S.fromList completedRules) (S.fromList actual)
        case redundantCompletion of
          KB.Complete system -> do
            check
              "every input equation is preserved"
              (all (\e -> Laws.withSides e (KB.equivalent system)) redundantPresentation)
            check
              "all final overlaps join"
              (all (\e -> Laws.withSides e (KB.equivalent system)) (KB.criticalPairs system))
          KB.Incomplete reason _ _ -> testFailed (show reason)
    , testProperty "category composition uses the completed rules" $ do
        let encode = emb Encode :: Value ~> Representation
            decode = emb Decode :: Representation ~> Value
            canonicalise = emb Canonicalise :: Representation ~> Representation
        expect "decode . encode" id (decode . encode)
        expect "encode . decode" canonicalise (encode . decode)
        expect "idempotence" canonicalise (canonicalise . canonicalise)
        expect "decoder" decode (decode . canonicalise . canonicalise)
        expect "encoder" encode (canonicalise . canonicalise . encode)
        expect "associativity" ((encode . decode) . encode) (encode . (decode . encode))
    , testProperty "normalisation preserves the concrete codec's meaning" $ do
        let raw = path Decode Canonicalise Encode Decode Canonicalise
            normal = KB.normalise codecSystem raw
        expect "five steps become one" "Decode" (show normal)
        check "integer inputs" (all (\n -> interpret raw n == interpret normal n) [-20 .. 20])
        check "all short value-to-value paths" (preserves [False, True] (paths 7 ValueSort ValueSort))
        check "all short value-to-representation paths" (preserves [False, True] (paths 7 ValueSort RepresentationSort))
        check "all short representation-to-value paths" (preserves [-4 .. 4] (paths 7 RepresentationSort ValueSort))
        check
          "all short representation-to-representation paths"
          (preserves [-4 .. 4] (paths 7 RepresentationSort RepresentationSort))
    , testProperty "the presented category has five normal forms" $ do
        let forms :: Sort a -> Sort b -> S.Set String
            forms a b = S.fromList (map (show P.. KB.normalise codecSystem) (paths 7 a b))
        expect "value endomorphisms" (S.singleton "id") (forms ValueSort ValueSort)
        expect "representations" (S.singleton "Encode") (forms ValueSort RepresentationSort)
        expect "values" (S.singleton "Decode") (forms RepresentationSort ValueSort)
        expect "representation endomorphisms" (S.fromList ["id", "Canonicalise"]) (forms RepresentationSort RepresentationSort)
    ]
