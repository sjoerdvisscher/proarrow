{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Compile laws and larger expressions in the same free syntax. The graph
-- compiler uses existing product, terminal, coproduct and closed signatures, with no diagram
-- instances for those structures.
module Examples.HypergraphRewrite (test) where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Constraint, Type)
import Data.Maybe (isJust, isNothing)
import Data.Type.Equality ((:~:))
import Data.Typeable (Typeable)
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (fst, id, snd, (**), (.))

import Proarrow.Category.Instance.Free
  ( Embed
  , FREE (..)
  , HasStructure (..)
  , StructureChild (..)
  , emb
  , structureChildren
  )
import Proarrow.Category.Instance.OpenHypergraph (Box (..), OPENHG, Wires, box, hypergraphParts, isomorphic)
import Proarrow.Category.Instance.Sub (SUBCAT (..))
import Proarrow.Category.Monoidal (Monoidal, SymMonoidal (..), SymMonoidalStructures, type (**))
import Proarrow.Category.Monoidal.Closed (Closed, ClosedStructures)
import Proarrow.Category.Monoidal.Closed qualified as C
import Proarrow.Colimit.BinaryCoproduct (HasBinaryCoproducts (..))
import Proarrow.Colimit.BinaryCoproduct qualified as Coproduct
import Proarrow.Core (Any, CAT, CategoryOf (..), Kind, Promonad (..), obj, type (+->))
import Proarrow.Limit.BinaryProduct (HasBinaryProducts (..), Struct (..))
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Initial (InitialProfunctor)
import Proarrow.Profunctor.Representable (Rep)
import Proarrow.Testing (check, expect)
import Proarrow.Tools.CCC qualified as CCC
import Proarrow.Tools.HypergraphRewrite
  ( CompiledRules
  , Direction (..)
  , NormalisationResult (..)
  , NormalisationStatus (..)
  , Parameter (..)
  , Rule
  , compileReducingRules
  , compileRules
  , normalise
  , parameterRulesWith
  , rewrites
  , rewritesWithDirection
  , ruleWith
  , subgraphRule
  , unlimitedRewrites
  )
import Proarrow.Tools.HypergraphRewrite.Free
  ( FREE_OB
  , FreeWire
  , NamedArrows (..)
  , StructureBox
  , freeLawRule
  , freeLawRuleWithDirection
  , freeLawRules
  , fromFreeWith
  )
import Proarrow.Tools.Laws
  ( Equation
  , Labelled (..)
  , Law (..)
  , LawBody
  , Laws (..)
  , ProEquation (..)
  , withSides
  , (===)
  )
import Proarrow.Tools.SMC qualified as SMC

-- A discrete base, restricted to the objects with runtime type evidence.
type data TYPES = TY Type
instance CategoryOf TYPES where
  type (~>) = (:~:)
  type Ob a = Any a

type SORT = SUBCAT (Typeable :: TYPES -> Constraint)
type T :: Type -> SORT
type T a = SUB (TY a)

-- All structures and both sides of rewriting use the same source category.
type Structures =
  '[NamedArrows, HasBinaryProducts, HasTerminalObject, HasBinaryCoproducts, Monoidal, SymMonoidal, Closed]
type Syntax = FREE Structures (InitialProfunctor :: CAT SORT)
instance Labelled Syntax where
  label _ f = f

type Diagram :: Type -> Type
type Diagram p = OPENHG FREE_OB (Either (StructureBox Structures) p)
type BoolWire = EMB (T Bool) :: Syntax
type IntWire = EMB (T Int) :: Syntax
type CharWire = EMB (T Char) :: Syntax
type PairWire = IntWire && CharWire
type SumWire = IntWire || CharWire
type TerminalWire = TerminalObject :: Syntax

graph :: (a :: Syntax) ~> b -> (FreeWire a :: Diagram String) ~> FreeWire b
graph = graphWith id

graphWith :: (String -> l) -> (a :: Syntax) ~> b -> (FreeWire a :: Diagram l) ~> FreeWire b
graphWith = fromFreeWith (\case {})

productRules, coproductRules :: Either String [(String, Rule FREE_OB (Either (StructureBox Structures) String))]
productRules =
  (++)
    <$> freeLawRules @'[HasBinaryProducts] @Structures
    <*> freeLawRules @'[HasTerminalObject] @Structures
coproductRules = freeLawRules @'[HasBinaryCoproducts] @Structures
compiledProductRules
  , compiledCoproductRules
    :: Either String (CompiledRules String FREE_OB (Either (StructureBox Structures) String))
compiledProductRules = productRules >>= compileRules
compiledCoproductRules = coproductRules >>= compileRules

-- Derived from pairing naturality and the projection laws. This combines their
-- derivation into a decreasing step for the CCC swap's concrete object types.
swapPairingFusion :: Either String (Rule FREE_OB (Either (StructureBox Structures) String))
swapPairingFusion =
  let f = namedArrow "f" :: PairWire ~> CharWire
      g = namedArrow "g" :: PairWire ~> IntWire
      h = namedArrow "h" :: PairWire ~> PairWire
      i = namedArrow "i" :: PairWire ~> PairWire
  in subgraphRule
       (\case Left operation -> Left (Left operation); Right name -> Right name)
       (graph ((f *** g) . (h &&& i)))
       (graph ((f . h) &&& (g . i)))

-- Only the two cancellation laws are needed here. The other closed laws test
-- naturality and the definition of the derived internal-hom action. That
-- definition expands identically on both sides in FREE, so it makes no progress.
closedRules :: Either String [(String, Rule FREE_OB (Either (StructureBox Structures) String))]
closedRules =
  traverse
    (\name -> (name,) <$> freeLawRule @ClosedStructures @Structures name)
    ["curry left inverse", "curry right inverse"]

coherenceRules :: Either String [(String, Rule FREE_OB (Either (StructureBox Structures) String))]
coherenceRules = do
  monoidal <-
    traverse
      (\name -> (name,) <$> freeLawRule @'[Monoidal] @Structures name)
      [ "tensor identity"
      , "leftUnitor tensor"
      , "rightUnitor tensor"
      , "leftUnitor left inverse"
      , "leftUnitor right inverse"
      , "rightUnitor left inverse"
      , "rightUnitor right inverse"
      , "associator left inverse"
      , "associator right inverse"
      ]
  swapRule <- freeLawRule @SymMonoidalStructures @Structures "swap self-inverse"
  pure (monoidal ++ [("swap self-inverse", swapRule)])

compiledClosedRules :: Either String (CompiledRules String FREE_OB (Either (StructureBox Structures) String))
compiledClosedRules = closedRuleSet >>= compileRules

closedRuleSet :: Either String [(String, Rule FREE_OB (Either (StructureBox Structures) String))]
closedRuleSet = concat <$> sequence [productRules, closedRules, coherenceRules]

-- * Normalisation examples

intArrow :: BoolWire ~> IntWire
intArrow = namedArrow "toInt"
charArrow :: BoolWire ~> CharWire
charArrow = namedArrow "toChar"
preprocess :: BoolWire ~> BoolWire
preprocess = namedArrow "preprocess"
pairedArrow :: BoolWire ~> PairWire
pairedArrow = namedArrow "paired"

productExpression :: BoolWire ~> ((PairWire && PairWire) && TerminalWire)
productExpression =
  ( ((fst . branches) &&& (snd . branches))
      &&& ((fst &&& snd) . ((fst . pairedArrow) &&& (snd . pairedArrow)))
  )
    &&& namedArrow "toTerminal"
  where
    branches = (intArrow . preprocess) &&& (charArrow . preprocess)
productNormalForm :: BoolWire ~> ((PairWire && PairWire) && TerminalWire)
productNormalForm = (((intArrow &&& charArrow) . preprocess) &&& pairedArrow) &&& terminate

type BodyInput = BoolWire ** IntWire
functionBody :: BodyInput ~> CharWire
functionBody = namedArrow "body"
functionArrow :: BoolWire ~> (IntWire C.~~> CharWire)
functionArrow = namedArrow "function"

beta :: (BodyInput ~> CharWire) -> BodyInput ~> CharWire
beta f = C.uncurry @IntWire @CharWire (C.curry @Syntax @BoolWire @IntWire f)
eta :: (BoolWire ~> (IntWire C.~~> CharWire)) -> BoolWire ~> (IntWire C.~~> CharWire)
eta f = C.curry @Syntax @BoolWire @IntWire (C.uncurry @IntWire @CharWire f)

closedExpression :: BodyInput ~> ((CharWire && CharWire) && TerminalWire)
closedExpression =
  ( (fst . (beta (beta functionBody) &&& (namedArrow "unused" :: BodyInput ~> IntWire)))
      &&& C.uncurry @IntWire @CharWire (eta (eta functionArrow))
  )
    &&& namedArrow "toTerminal"
closedNormalForm :: BodyInput ~> ((CharWire && CharWire) && TerminalWire)
closedNormalForm = (functionBody &&& C.uncurry @IntWire @CharWire functionArrow) &&& terminate

-- Projection-style swap, compiled with an embedded product input rather than
-- destructuring the input tuple in Haskell.
cccSwap :: PairWire ~> (CharWire && IntWire)
cccSwap =
  CCC.toCCC @(CCC.F PairWire) @(CCC.F CharWire CCC.:** CCC.F IntWire)
    (\p -> (CCC.liftF snd p, CCC.liftF fst p))

smcSwap :: (IntWire ** CharWire) ~> (CharWire ** IntWire)
smcSwap =
  SMC.toSMC @(SMC.F IntWire SMC.:** SMC.F CharWire) @(SMC.F CharWire SMC.:** SMC.F IntWire)
    (\ds -> SMC.lam (\(a, b) -> (b, a)) SMC.! ds)

fromInt :: IntWire ~> BoolWire
fromInt = namedArrow "fromInt"
fromChar :: CharWire ~> BoolWire
fromChar = namedArrow "fromChar"
postprocess :: BoolWire ~> BoolWire
postprocess = namedArrow "postprocess"
collectedArrow :: SumWire ~> BoolWire
collectedArrow = namedArrow "collected"

coproductExpression :: (SumWire || SumWire) ~> BoolWire
coproductExpression =
  ((branches . lft) ||| (branches . rgt))
    ||| (((collectedArrow . lft) ||| (collectedArrow . rgt)) . (lft ||| rgt))
  where
    branches = (postprocess . fromInt) ||| (postprocess . fromChar)
coproductNormalForm :: (SumWire || SumWire) ~> BoolWire
coproductNormalForm = (postprocess . (fromInt ||| fromChar)) ||| collectedArrow

-- * Test support

-- A small additional structure checks both orientations and selection errors.
type HasTwist :: Kind -> Constraint
class (CategoryOf k) => HasTwist k where
  twist :: (Ob (a :: k)) => a ~> a
instance (NamedArrows (FREE cs p)) => HasTwist (FREE cs p) where
  twist = namedArrow "twist"
instance Laws '[HasTwist] where
  laws =
    [ Law "expand" \ @a _ -> obj @a === twist . twist
    , Law "duplicate" \ @a _ -> obj @a === twist . twist
    , Law "duplicate" \ @a _ -> obj @a === twist . twist
    ]

interpretTwist :: LawBody '[HasTwist] -> Equation (Diagram String)
interpretTwist body =
  withSides
    (runIdentity (body @BoolWire @BoolWire @BoolWire @BoolWire @BoolWire (\name -> Identity (namedArrow name))))
    (\lhs rhs -> graph lhs :=: graph rhs)

-- This expansion creates a product object that is absent from the left side.
instance Laws '[HasBinaryProducts, HasTwist] where
  laws =
    [ Law "expand output" \ @a @b mor -> do
        f <- mor @a @b "f"
        f === fst @_ @b @b . (f &&& f)
    ]

-- A base quiver also works; named arrows are useful for compound endpoints.
type Base :: CAT SORT
data Base a b where
  Base :: (Ob a, Ob b) => String -> Base a b
instance Show (Base a b) where
  show (Base name) = show name

closeDiagram :: (a :: Diagram String) ~> b -> (Wires '[] :: Diagram String) ~> Wires '[]
closeDiagram f@Objs = box (Right "sink") . f . box (Right "source")

checkNormalisation
  :: CompiledRules String FREE_OB (Either (StructureBox Structures) String)
  -> (a :: Syntax) ~> b
  -> a ~> b
  -> Property ()
checkNormalisation compiled original expected = do
  let result = normalise unlimitedRewrites compiled (closeDiagram (graph original))
  expect "normal form reached" NormalForm (normalisationStatus result)
  check "wrong normal form in context" (isomorphic (closeDiagram (graph expected)) (normalisedGraph result))
  check "no reduction applied" (normalisationRewrites result > 0)
  expect
    "normalising again does no work"
    0
    (normalisationRewrites (normalise unlimitedRewrites compiled (normalisedGraph result)))

childName :: (a :: Syntax) ~> b -> String
childName f = case hypergraphParts (graph f) of
  (_, _, _, [Box (Right name) _ _]) -> name
  _ -> "not one generator"

test :: TestTree
test =
  testGroup
    "Law rewriting"
    [ testGroup
        "Compilation"
        [ testProperty "compilation preserves identity and composition" $ do
            check "identity gained a box" (isomorphic (graph (obj @BoolWire)) id)
            check
              "composition changed graph connections"
              (isomorphic (graph (intArrow . preprocess)) (graph intArrow . graph preprocess))
        , testProperty "base generators compile inside structural children" $
            let f = emb (Base "base") :: (EMB (T Bool) :: FREE Structures Base) ~> EMB (T Int)
                term = f &&& f
                (_, _, _, boxes) = hypergraphParts (fromFreeWith (\(Base name) -> name) id term)
            in expect "base labels survive" ["base", "base"] [name | Box (Right name) _ _ <- boxes]
        ]
    , testGroup
        "Normalisation"
        [ testProperty "products and coproducts share one compiled rule set" $ do
            compiled <- either testFailed pure (((++) <$> productRules <*> coproductRules) >>= compileRules)
            let original = (fst . (intArrow &&& charArrow)) . ((fromInt ||| fromChar) . lft)
                result = normalise unlimitedRewrites compiled (graph (original &&& original))
                expected = (obj @IntWire &&& obj @IntWire) . intArrow . fromInt
            expect "normal form reached" NormalForm (normalisationStatus result)
            check "no rewrites applied" (normalisationRewrites result > 0)
            check "wrong mixed normal form" (isomorphic (graph expected) (normalisedGraph result))
        , testProperty "all coproduct laws normalise a larger expression" $ do
            compiled <- either testFailed pure compiledCoproductRules
            checkNormalisation compiled coproductExpression coproductNormalForm
        , testProperty "product normalisation preserves the surrounding graph" $ do
            compiled <- either testFailed pure compiledProductRules
            checkNormalisation compiled productExpression productNormalForm
        ]
    , testGroup
        "Closed structure"
        [ testProperty "CCC projection swap reduces with decreasing box count" $ do
            rules <- either testFailed pure (freeLawRules @'[HasBinaryProducts] @Structures)
            fusion <- either testFailed pure swapPairingFusion
            compiled <- either testFailed pure (compileReducingRules (("pairing fusion", fusion) : rules))
            checkNormalisation compiled cccSwap (snd &&& fst)
        , testProperty "SMC applied swap reduces with decreasing box count" $ do
            compiled <- either testFailed pure (closedRuleSet >>= compileReducingRules)
            checkNormalisation compiled smcSwap (swap @Syntax @IntWire @CharWire)
        , testProperty "beta and eta simplify with products and terminal objects" $ do
            compiled <- either testFailed pure compiledClosedRules
            checkNormalisation compiled closedExpression closedNormalForm
        , testProperty "eta cancellation captures a composite function" $ do
            compiled <- either testFailed pure compiledClosedRules
            checkNormalisation compiled (eta (functionArrow . preprocess)) (functionArrow . preprocess)
        ]
    , testGroup
        "Terminal objects"
        [ testProperty "terminal uniqueness rewrites generators with compound domains" $ do
            r <- either testFailed pure (freeLawRule @'[HasTerminalObject] @Structures "uniqueness")
            let host = graph (namedArrow "discardPair" :: PairWire ~> TerminalWire)
                expected = graph (terminate @Syntax @PairWire)
                results = rewrites r host
            expect "one terminal rewrite" 1 (length results)
            check "wrong terminal normal form" (all (isomorphic expected) results)
        , testProperty "terminal uniqueness preserves nonterminal outputs" $ do
            r <- either testFailed pure (freeLawRule @'[HasTerminalObject] @Structures "uniqueness")
            expect "ordinary generator retained" 0 (length (rewrites r (graph intArrow)))
        ]
    , testGroup
        "Object parameters"
        [ testProperty "one rule handles different instantiations in one batch" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts] @Structures "fst")
            compiled <- either testFailed pure (compileRules [("fst", r)])
            let host = (fst . (intArrow &&& charArrow)) &&& (fst . (preprocess &&& preprocess))
                result = normalise unlimitedRewrites compiled (graph host)
            expect "both instantiations rewritten" 2 (normalisationRewrites result)
            expect "compatible matches share one batch" 1 (normalisationBatches result)
            check "wrong normal form" (isomorphic (graph (intArrow &&& preprocess)) (normalisedGraph result))
        , testProperty "object variables bind whole products and coproducts" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts] @Structures "fst")
            let g = namedArrow "summed" :: BoolWire ~> SumWire
                host = graph (fst . (pairedArrow &&& g))
                results = rewrites r host
            expect "one match" 1 (length results)
            check "compound binding lost" (all (isomorphic (graph pairedArrow)) results)
        , testProperty "shared object variables reject inconsistent arrow types" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts] @Structures "pairing naturality")
            let h = namedArrow "preprocess" :: BoolWire ~> IntWire
                g = namedArrow "toChar" :: IntWire ~> CharWire
                host = graph ((intArrow . preprocess) &&& (g . h))
            expect "incompatible intermediate types matched" 0 (length (rewrites r host))
        , testProperty "replacement constructs fresh compound object sorts" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts, HasTwist] @Structures @String "expand output")
            let checkExpansion :: forall (a :: Syntax) b. a ~> b -> Property ()
                checkExpansion f@Objs = do
                  let host = graph f
                      expected = graph (fst @Syntax @b @b . (f &&& f))
                      results = rewrites r host
                  expect "one expansion" 1 (length results)
                  check "wrong reflected replacement sorts" (all (isomorphic expected) results)
            checkExpansion intArrow
            checkExpansion pairedArrow
            checkExpansion (namedArrow "summed" :: BoolWire ~> SumWire)
        , testProperty "object parameters work with a different source quiver" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts] @Structures "fst")
            let f = emb (Base "f") :: (EMB (T Bool) :: FREE Structures Base) ~> EMB (T Int)
                g = emb (Base "g") :: (EMB (T Bool) :: FREE Structures Base) ~> EMB (T Char)
                host = fromFreeWith (\(Base name) -> name) id (fst . (f &&& g))
                expected = fromFreeWith (\(Base name) -> name) id f
                results = rewrites r host
            expect "one base-generator cancellation" 1 (length results)
            check "source category changed" (all (isomorphic expected) results)
        ]
    , testGroup
        "Traversal"
        [ testProperty "coproduct traversal exposes both branches in order" $
            let original = Coproduct.Sum fromInt fromChar
                (names, rebuilt) = foldStructure @_ @_ @_ @_ @(Rep (Embed :: SORT +-> Syntax)) (\child@Objs -> ([childName child], child)) original
            in do
                 expect "visited once in order" ["fromInt", "fromChar"] names
                 expect
                   "enumeration agrees with traversal"
                   names
                   [childName child | StructureChild child <- structureChildren original]
                 check "rebuilt syntax changed" (isomorphic (graph (fromInt ||| fromChar)) (graph rebuilt))
        , testProperty "coproduct traversal sequences effects only for children" $ do
            check
              "ignored a failing child traversal"
              (isNothing (foldStructure @_ @_ @_ @_ @(Rep (Embed :: SORT +-> Syntax)) (const Nothing) (Coproduct.Sum fromInt fromChar)))
            check
              "visited a child of an injection"
              (isJust (foldStructure @_ @_ @_ @_ @(Rep (Embed :: SORT +-> Syntax)) (const Nothing) (Coproduct.Lft @IntWire @CharWire)))
        , testProperty "coproduct operations compare independently of branches" $ do
            let mixed = Coproduct.Sum fromInt fromChar
                equalSorts = Coproduct.Sum postprocess postprocess
            check "copairing operation depends on child data" (sameStructure mixed equalSorts)
            check
              "different injections compare equal"
              (not (sameStructure (Coproduct.Lft @IntWire @CharWire) (Coproduct.Rgt @IntWire @CharWire)))
            check "copairing compares equal to an injection" (not (sameStructure mixed (Coproduct.Lft @IntWire @CharWire)))
        , testProperty "structure traversal visits immediate children in order" $
            let original = Prd intArrow charArrow
                (names, rebuilt) = foldStructure @_ @_ @_ @_ @(Rep (Embed :: SORT +-> Syntax)) (\child@Objs -> ([childName child], child)) original
            in do
                 expect "visited once in order" ["toInt", "toChar"] names
                 expect
                   "enumeration agrees with traversal"
                   names
                   [childName child | StructureChild child <- structureChildren original]
                 check "rebuilt syntax changed" (isomorphic (graph (intArrow &&& charArrow)) (graph rebuilt))
        , testProperty "structure traversal sequences effects only for children" $ do
            check
              "ignored a failing child traversal"
              (isNothing (foldStructure @_ @_ @_ @_ @(Rep (Embed :: SORT +-> Syntax)) (const Nothing) (Prd intArrow charArrow)))
            check
              "visited a child of a projection"
              (isJust (foldStructure @_ @_ @_ @_ @(Rep (Embed :: SORT +-> Syntax)) (const Nothing) (Fst @IntWire @CharWire)))
        , testProperty "structure operations compare independently of children and sorts" $ do
            let mixed = Prd intArrow charArrow
                equalSorts = Prd preprocess preprocess
            check "pairing operation depends on child data" (sameStructure mixed equalSorts)
            check "different projections compare equal" (not (sameStructure (Fst @IntWire @CharWire) (Snd @IntWire @CharWire)))
            check "pairing compares equal to a projection" (not (sameStructure mixed (Fst @IntWire @CharWire)))
        ]
    , testGroup
        "Matching"
        [ testProperty "product projection captures composite branches" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts] @Structures "fst")
            let retained = intArrow . preprocess
                discarded = (charArrow . preprocess) &&& pairedArrow
                results = rewrites r (graph (fst . (retained &&& discarded)))
            expect "one composite projection" 1 (length results)
            check "composite branch changed" (all (isomorphic (graph retained)) results)
        , testProperty "generator names cannot collide with structural skeletons" $ do
            r <- either testFailed pure (freeLawRule @'[HasBinaryProducts] @Structures "fst")
            let generator = namedArrow (show (Fst @IntWire @CharWire)) :: BoolWire ~> IntWire
                results = rewrites r (graph (fst . (generator &&& charArrow)))
            expect "one projection" 1 (length results)
            check "generator mistaken for a structural operation" (all (isomorphic (graph generator)) results)
        ]
    , testGroup
        "Law selection"
        [ testProperty "reversed product projection rejects unbound parameters" $
            case freeLawRuleWithDirection @'[HasBinaryProducts] @Structures @String "fst" RightToLeft of
              Left err -> expect "unbound g" "subgraphRule: unbound arrow parameter on the right" err
              Right _ -> testFailed "accepted unbound replacement parameter"
        , testProperty "RightToLeft reverses the equation as written" $
            case rewritesWithDirection @'[HasTwist]
              "expand"
              RightToLeft
              interpretTwist
              (closeDiagram (graph (twist @Syntax @BoolWire . twist))) of
              Left err -> testFailed err
              Right results -> do
                expect "one cancellation" 1 (length results)
                check "wrong result" (all (isomorphic (closeDiagram (graph (obj @BoolWire)))) results)
        , testProperty "default direction reports unsupported left boundaries" $
            case ruleWith @'[HasTwist] "expand" interpretTwist of
              Left _ -> pure ()
              Right _ -> testFailed "accepted the identity as an injective left interface"
        , testProperty "unknown names fail before interpreting the law" $
            case ruleWith @'[HasTwist] "missing" (\_ -> error "interpreted missing law") of
              Left err -> expect "unknown name" "ruleWith: unknown law \"missing\"" err
              Right _ -> testFailed "accepted unknown name"
        , testProperty "all-law compilation rejects duplicate names" $
            case parameterRulesWith @'[HasTwist] @_ @_ @String
              (\_ -> let term = graphWith Variable preprocess in term :=: term) of
              Left err -> expect "ambiguous name" "ruleWith: ambiguous law \"duplicate\"" err
              Right _ -> testFailed "accepted duplicate rule names"
        , testProperty "ambiguous names fail before interpreting the law" $
            case ruleWith @'[HasTwist] "duplicate" (\_ -> error "interpreted ambiguous law") of
              Left err -> expect "ambiguous name" "ruleWith: ambiguous law \"duplicate\"" err
              Right _ -> testFailed "accepted ambiguous name"
        ]
    ]
