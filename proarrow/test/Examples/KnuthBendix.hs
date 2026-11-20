-- | Completion for a codec with two object colours. Decoding an encoding is an
-- identity; encoding a decoding canonicalises the representation. Completion
-- derives idempotence and the two ways to remove redundant canonicalisation.
-- Its value object is both initial and terminal; enumeration supplies the
-- universal arrows and the generators for the built-in law tests.
module Examples.KnuthBendix (test, Codec (..), codecSystem, completedRules, redundantRules) where

import Data.Kind (Constraint, Type)
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Data.Typeable (Typeable)
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))
import Prelude qualified as P

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), Rewrite (..), emb, path)
import Proarrow.Category.Instance.Sub (SUBCAT (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN)
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (SomeOb, SomeOf (..))
import Proarrow.Testing
  ( Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow
  , check
  , expect
  , genSomeDef
  , optGen
  )
import Proarrow.Testing.Laws (testInitialObject, testTerminalObject)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.KnuthBendix.NormalForms qualified as NF
import Proarrow.Tools.Laws (ProEquation ((:=:)))
import Proarrow.Tools.Laws qualified as Laws

-- Only these two Haskell types are vertices of the presented category.
type Sort :: Type -> Type
data Sort a where
  ValueSort :: Sort Bool
  RepresentationSort :: Sort Int

type IsCodec :: Type -> Constraint
class (Typeable a) => IsCodec a where
  codecSort :: Sort a
instance IsCodec Bool where codecSort = ValueSort
instance IsCodec Int where codecSort = RepresentationSort

type Codec :: CAT (SUBCAT IsCodec)
data Codec a b where
  Encode :: Codec (SUB Bool) (SUB Int)
  Decode :: Codec (SUB Int) (SUB Bool)
  Canonicalise :: Codec (SUB Int) (SUB Int)

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

objects :: [SomeOb (SUBCAT IsCodec)]
objects = [Some @(SUB Bool), Some @(SUB Int)]

normalForms :: NF.NormalForms Codec
normalForms = case NF.compile objects [NF.Generator Encode, NF.Generator Decode, NF.Generator Canonicalise] completion of
  Just forms -> forms
  Nothing -> error "codec normal-form compilation failed"

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

type Value = PTH (SUB Bool) :: PATHS Codec
type Representation = PTH (SUB Int) :: PATHS Codec

-- The universal arrows are the unique normal forms discovered above.
instance HasInitialObject (PATHS Codec) where
  type InitialObject = Value
  initiate @a = unique (NF.enumerate @(SUB Bool) @(UN PTH a) normalForms)

instance HasTerminalObject (PATHS Codec) where
  type TerminalObject = Value
  terminate @a = unique (NF.enumerate @(UN PTH a) @(SUB Bool) normalForms)

unique :: Maybe [a] -> a
unique (Just [p]) = p
unique _ = error "expected a unique codec arrow"

instance Testable (PATHS Codec) where
  type TestOb a = Ob a
  showOb @a = case codecSort @(UN SUB (UN PTH a)) of
    ValueSort -> "Value"
    RepresentationSort -> "Representation"
  genSome = genSomeDef @'[Value, Representation]
instance TestingEqShow (Paths (a :: PATHS Codec) b)
instance (Ob a, Ob b) => TestableType (Paths (a :: PATHS Codec) b) where
  gen = optGen (fromMaybe (error "missing codec endpoint") (NF.enumerate @(UN PTH a) @(UN PTH b) normalForms))
instance TestableProfunctor (Paths :: CAT (PATHS Codec))

interpret :: Paths (PTH (SUB a) :: PATHS Codec) (PTH (SUB b)) -> a -> b
interpret PNil = P.id
interpret (PCons Encode more) = fromEnum . interpret more
interpret (PCons Decode more) = odd . interpret more
interpret (PCons Canonicalise more) = (`mod` 2) . interpret more

-- Enumerate raw paths independently of the normalising composition instance.
paths :: forall a b. Int -> Sort a -> Sort b -> [Paths (PTH (SUB a) :: PATHS Codec) (PTH (SUB b))]
paths n a b = identities ++ if n <= 0 then [] else steps
  where
    identities :: [Paths (PTH (SUB a) :: PATHS Codec) (PTH (SUB b))]
    identities = case (a, b) of
      (ValueSort, ValueSort) -> [PNil]
      (RepresentationSort, RepresentationSort) -> [PNil]
      _ -> []
    steps :: [Paths (PTH (SUB a) :: PATHS Codec) (PTH (SUB b))]
    steps = case b of
      ValueSort -> [PCons Decode p | p <- paths (n - 1) a RepresentationSort]
      RepresentationSort ->
        [PCons Encode p | p <- paths (n - 1) a ValueSort]
          ++ [PCons Canonicalise p | p <- paths (n - 1) a RepresentationSort]

preserves :: (Eq b) => [a] -> [Paths (PTH (SUB a) :: PATHS Codec) (PTH (SUB b))] -> Bool
preserves inputs = all $ \p ->
  let normal = KB.normalise codecSystem p
  in all (\x -> interpret p x == interpret normal x) inputs

test :: TestTree
test =
  testGroup
    "Coloured KB codec"
    [ testInitialObject @(PATHS Codec)
    , testTerminalObject @(PATHS Codec)
    , testProperty "completion derives three useful codec equations" $ do
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
    , testProperty "enumeration finds five arrows and a zero object" $ do
        expect "value endomorphisms" (Just ["id"]) (fmap (map show) (NF.enumerate @(SUB Bool) @(SUB Bool) normalForms))
        expect "representations" (Just ["Encode"]) (fmap (map show) (NF.enumerate @(SUB Bool) @(SUB Int) normalForms))
        expect "values" (Just ["Decode"]) (fmap (map show) (NF.enumerate @(SUB Int) @(SUB Bool) normalForms))
        expect
          "representation endomorphisms"
          (Just ["id", "Canonicalise"])
          (fmap (map show) (NF.enumerate @(SUB Int) @(SUB Int) normalForms))
        expect "representation endomorphism count" (Just (NF.Finite 2)) (NF.cardinality @(SUB Int) @(SUB Int) normalForms)
        expect "initial object" [Some @(SUB Bool)] (NF.initialObjects normalForms)
        expect "terminal object" [Some @(SUB Bool)] (NF.terminalObjects normalForms)
    ]
