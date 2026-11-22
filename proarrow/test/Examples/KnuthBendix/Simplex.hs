{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Face/degeneracy rewriting following Mathlib's
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/Basic.html generators and relations>
-- presentation.
-- Mathlib's [n] has n+1 elements; our object n
-- has n elements. Face also includes the augmentation 0 -> 1.
--
-- Complete the finite presentation on sizes 0 through 4 using shortlex.
-- Its normal forms need not follow Mathlib's index convention; interpretations
-- into Simplex check that they represent every monotone map uniquely.
module Examples.KnuthBendix.Simplex (test, Generator (..), equations, system, completedRules, generators, generatorMap, rank) where

import Data.Fin (Fin (..), absurd, toNatural, universe, weakenLeft1)
import Data.Nat qualified as N
import Data.Proxy (Proxy (..))
import Data.Set qualified as S
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3, Nat4, Nat5, reflect)
import Data.Typeable (eqT)
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, (.))

import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), path)
import Proarrow.Category.Instance.Simplex (Forget, IsNat (..), Nat (..), SNat (..), Simplex (..), suc)
import Proarrow.Category.Topos (HasEpiMonoFactorization (..))
import Proarrow.Colimit.Initial (HasInitialObject (..))
import Proarrow.Core (CAT, Promonad (..), UN)
import Proarrow.Functor qualified as F
import Proarrow.Limit.Terminal (HasTerminalObject (..))
import Proarrow.Object (SomeOb, SomeOf (..), pattern Objs)
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.KnuthBendix.NormalForms qualified as NF
import Proarrow.Tools.Laws (ProEquation ((:=:)))
import Proarrow.Tools.Laws qualified as Laws

type Generator :: CAT Nat
data Generator a b where
  Face :: forall n. (IsNat n) => Fin (S n) -> Generator n (S n)
  Degeneracy :: forall n. (IsNat n) => Fin (S n) -> Generator (S (S n)) (S n)

dimension :: forall n. (IsNat n) => Integer
dimension = toInteger (N.toNatural (reflect (Proxy @n)))

instance Show (Generator a b) where
  show (Face @n i) = "Face[" ++ show (dimension @n) ++ "," ++ show i ++ "]"
  show (Degeneracy @n i) = "Degeneracy[" ++ show (dimension @n + 1) ++ "," ++ show i ++ "]"

instance EqGen Generator where
  eqGen (Face @n i) (Face @m j) = case eqT @n @m of
    Just Refl | i == j -> Just Refl
    _ -> Nothing
  eqGen (Degeneracy @n i) (Degeneracy @m j) = case eqT @n @m of
    Just Refl | i == j -> Just Refl
    _ -> Nothing
  eqGen _ _ = Nothing

rank :: Generator a b -> (Int, Integer, Integer)
rank (Face @n i) = (0, dimension @n, toInteger (toNatural i))
rank (Degeneracy @n i) = (1, dimension @n, toInteger (toNatural i))

-- Mathlib's delta_comp_delta, with the two composites read right-to-left.
faceFaces :: forall n. (IsNat n) => [KB.Equation Generator]
faceFaces =
  [ path (Face @(S n) (FS j)) (Face @n i) :=: path (Face @(S n) (weakenLeft1 i)) (Face @n j)
  | i <- universe @(S n)
  , j <- universe @(S n)
  , i <= j
  ]

-- delta_comp_sigma_self and delta_comp_sigma_succ.
cancellations :: forall n. (IsNat n) => [KB.Equation Generator]
cancellations =
  concat
    [ [ path (Degeneracy @n i) (Face @(S n) (weakenLeft1 i)) :=: path
      , path (Degeneracy @n i) (Face @(S n) (FS i)) :=: path
      ]
    | i <- universe @(S n)
    ]

-- delta_comp_sigma_of_le and delta_comp_sigma_of_gt. The smaller middle
-- ordinal on the right is the image in the epi-mono factorization.
mixed :: forall n. (IsNat n) => [KB.Equation Generator]
mixed =
  [ ( if i <= weakenLeft1 j
        then path (Degeneracy @(S n) (FS j)) (Face @(S (S n)) (weakenLeft1 i))
        else path (Degeneracy @(S n) (weakenLeft1 j)) (Face @(S (S n)) (FS i))
    )
      :=: path (Face @(S n) i) (Degeneracy @n j)
  | i <- universe @(S (S n))
  , j <- universe @(S n)
  ]

-- sigma_comp_sigma.
degeneracyDegeneracies :: forall n. (IsNat n) => [KB.Equation Generator]
degeneracyDegeneracies =
  [ path (Degeneracy @n j) (Degeneracy @(S n) (weakenLeft1 i))
      :=: path (Degeneracy @n i) (Degeneracy @(S n) (FS j))
  | i <- universe @(S n)
  , j <- universe @(S n)
  , i <= j
  ]

-- | All simplicial relations involving only ordinals of size at most n.
-- Each recursive step adds relations whose largest ordinal has size n.
equations :: forall n. (IsNat n) => [KB.Equation Generator]
equations = ifS @n \ @pn ->
  equations @pn ++ ifS @pn \ @ppn ->
    faceFaces @ppn ++ cancellations @ppn ++ ifS @ppn \ @pppn ->
      mixed @pppn ++ degeneracyDegeneracies @pppn
  where
    ifS :: forall x a. (IsNat x) => (forall px. (IsNat px) => [a]) -> [a]
    ifS f = case singNat @x of
      SZ -> []
      SS @px -> f @px

completion :: KB.Completion Generator
completion = KB.completeWithOrder rank (KB.Limits 500 10000) (equations @Nat4)

system :: KB.System Generator
system = case completion of
  KB.Complete s -> s
  KB.Incomplete reason _ _ -> error ("simplex completion: " ++ show reason)

completedRules :: [String]
completedRules = [KB.withRule r (\l rhs -> show l ++ " -> " ++ show rhs) | r <- KB.rules system]

face :: forall n. (IsNat n) => Fin (S n) -> Simplex n (S n)
face FZ = Y id
face (FS i) = case singNat @n of
  SZ -> absurd i
  SS @m -> suc (face @m i)

degeneracy :: forall n. (IsNat n) => Fin (S n) -> Simplex (S (S n)) (S n)
degeneracy FZ = X id
degeneracy (FS i) = case singNat @n of
  SZ -> absurd i
  SS @m -> suc (degeneracy @m i)

generatorMap :: Generator a b -> Simplex a b
generatorMap (Face i) = face i
generatorMap (Degeneracy i) = degeneracy i

-- Check the usual meanings of the indices independently of the X/Y recursion.
generatorCorrect :: Generator a b -> Bool
generatorCorrect (Face @n i) =
  images (face i) == [if k < toInteger (toNatural i) then k else k + 1 | k <- [0 .. dimension @n - 1]]
generatorCorrect (Degeneracy @n i) =
  images (degeneracy i) == [if k <= toInteger (toNatural i) then k else k - 1 | k <- [0 .. dimension @n + 1]]

images :: forall a b. (IsNat a, IsNat b) => Simplex a b -> [Integer]
images f = map (toInteger . toNatural . F.fmap @Forget f) (universe @a)

interpret :: Paths (a :: PATHS Generator) b -> Simplex (UN PTH a) (UN PTH b)
interpret PNil = id
interpret (PCons g more) = generatorMap g . interpret more

objects :: [SomeOb Nat]
objects = [Some @Nat0, Some @Nat1, Some @Nat2, Some @Nat3, Some @Nat4]

generators :: [NF.Generator Generator]
generators = concatMap atSize objects
  where
    atSize :: SomeOb Nat -> [NF.Generator Generator]
    atSize (Some @n) =
      [NF.Generator (Face @n i) | dimension @n < 4, i <- universe @(S n)]
        ++ [NF.Generator (Degeneracy @n i) | dimension @n + 2 <= 4, i <- universe @(S n)]

normalForms :: NF.NormalForms Generator
normalForms = case NF.compile objects generators completion of
  Just forms -> forms
  Nothing -> error "simplex normal-form compilation failed"

data SomePath where
  SomePath :: forall a b. (IsNat a, IsNat b) => Paths (PTH a :: PATHS Generator) (PTH b) -> SomePath

modelKey :: SomePath -> (Integer, Integer, String)
modelKey (SomePath @a @b p) = (dimension @a, dimension @b, show (interpret p))

-- Independent enumeration of every X/Y map between two ordinals.
simplexMaps :: forall a b. (IsNat a, IsNat b) => [Simplex a b]
simplexMaps = case (singNat @a, singNat @b) of
  (SZ, SZ) -> [ZZ]
  (SS, SZ) -> []
  (_, SS @b') ->
    [Y f | f <- simplexMaps @a @b'] ++ case singNat @a of
      SZ -> []
      SS @a' -> [X f | f <- simplexMaps @a' @b]

expectedMaps :: S.Set (Integer, Integer, String)
expectedMaps =
  S.fromList
    [(dimension @a, dimension @b, show f) | Some @a <- objects, Some @b <- objects, f <- simplexMaps @a @b]

test :: TestTree
test =
  testGroup
    "Simplex face/degeneracy rewriting"
    [ testProperty "Mathlib's simplicial identities hold in Simplex" $ do
        check "a generator has the wrong monotone map" (all (\(NF.Generator g) -> generatorCorrect g) generators)
        expect "no relations below size 2" 0 (length (equations @Nat0) + length (equations @Nat1))
        check
          "an incorrectly indexed relation"
          (all (\e -> Laws.withSides e (\l r -> interpret l == interpret r)) (equations @Nat5))
    , testProperty "discovers binary products and coproducts with their legs" $ do
        () <- case NF.binaryProducts @Nat2 @Nat1 normalForms of
          Just [NF.Cone @x left right] -> case eqT @x @Nat2 of
            Just Refl -> do
              expect "product projection to 2" id (interpret left)
              expect "product projection to 1" terminate (interpret right)
            Nothing -> testFailed "2 × 1 has the wrong apex"
          _ -> testFailed "expected one product cone for 2 × 1"
        () <- case NF.binaryCoproducts @Nat0 @Nat2 normalForms of
          Just [NF.Cocone @x left right] -> case eqT @x @Nat2 of
            Just Refl -> do
              expect "coproduct injection from 0" initiate (interpret left)
              expect "coproduct injection from 2" id (interpret right)
            Nothing -> testFailed "0 + 2 has the wrong apex"
          _ -> testFailed "expected one coproduct cocone for 0 + 2"
        expect "2 × 2 has no product" (Just 0) (length <$> NF.binaryProducts @Nat2 @Nat2 normalForms)
        expect "2 + 2 has no coproduct" (Just 0) (length <$> NF.binaryCoproducts @Nat2 @Nat2 normalForms)
    , testProperty "discovers the equalizer and coequalizer of the two points of 2" $ do
        let f = PCons (Face @Nat1 FZ) PNil
            g = PCons (Face @Nat1 (FS FZ)) PNil
        () <- case NF.equalizers normalForms f g of
          Just [NF.Equalizer @x leg] -> case eqT @x @Nat0 of
            Just Refl -> expect "empty inclusion into 1" initiate (interpret leg)
            Nothing -> testFailed "the points have no common value"
          _ -> testFailed "expected one equalizer"
        case NF.coequalizers normalForms f g of
          Just [NF.Coequalizer @x leg] -> case eqT @x @Nat1 of
            Just Refl -> expect "collapse 2 to 1" terminate (interpret leg)
            Nothing -> testFailed "the two points should collapse to one"
          _ -> testFailed "expected one coequalizer"
    , testProperty "discovers pullback and pushout squares for two point inclusions" $ do
        let lastPoint = PCons (Face @Nat1 FZ) PNil
            firstPoint = PCons (Face @Nat1 (FS FZ)) PNil
        () <- case NF.pullbacks normalForms lastPoint firstPoint of
          Just [NF.Cone @x left right] -> case eqT @x @Nat0 of
            Just Refl -> do
              expect "left projection from 0" initiate (interpret left)
              expect "right projection from 0" initiate (interpret right)
            Nothing -> testFailed "the point inclusions are disjoint"
          _ -> testFailed "expected one pullback square"
        () <- case NF.pushouts normalForms lastPoint firstPoint of
          Just [NF.Cocone @x left right] -> case eqT @x @Nat3 of
            Just Refl -> do
              expect "left inclusion into the first two points" (generatorMap (Face @Nat2 (FS (FS FZ)))) (interpret left)
              expect "right inclusion into the last two points" (generatorMap (Face @Nat2 FZ)) (interpret right)
            Nothing -> testFailed "the two copies of 2 share one point"
          _ -> testFailed "expected one pushout square"
        expect
          "gluing the first points has no pushout"
          (Just 0)
          (length <$> NF.pushouts normalForms firstPoint firstPoint)
    , testProperty "completion gives one normal form for every monotone map" $ do
        case completion of
          KB.Complete _ -> pure ()
          KB.Incomplete reason _ _ -> testFailed (show reason)
        let expectedCount :: forall a b. (IsNat a, IsNat b) => NF.Cardinality
            expectedCount = NF.Finite (fromIntegral (length (simplexMaps @a @b)))
            counts :: [(Maybe NF.Cardinality, Maybe NF.Cardinality)]
            counts =
              [ (Just (expectedCount @a @b), NF.cardinality @a @b normalForms)
              | Some @a <- objects
              , Some @b <- objects
              ]
            forms :: [SomePath]
            forms = [SomePath p | Some @a <- objects, Some @b <- objects, Just ps <- [NF.enumerate @a @b normalForms], p <- ps]
        expect "hom-set cardinalities" (map fst counts) (map snd counts)
        check
          "source-wide counts"
          ( and
              [ NF.cardinalitiesFrom @a normalForms
                  == Just [(target, expectedCount @a @b) | target@(Some @b) <- objects]
              | Some @a <- objects
              ]
          )
        check
          "target-wide counts"
          ( and
              [ NF.cardinalitiesTo @b normalForms
                  == Just [(source, expectedCount @a @b) | source@(Some @a) <- objects]
              | Some @b <- objects
              ]
          )
        expect "initial object" [Some @(InitialObject :: Nat)] (NF.initialObjects normalForms)
        expect "terminal object" [Some @(TerminalObject :: Nat)] (NF.terminalObjects normalForms)
        check
          "discovered initial arrows agree with initiate"
          ( and
              [ fmap (map interpret) (NF.enumerate @(InitialObject :: Nat) @a normalForms) == Just [initiate @Nat @a]
              | Some @a <- objects
              ]
          )
        check
          "discovered terminal arrows agree with terminate"
          ( and
              [ fmap (map interpret) (NF.enumerate @a @(TerminalObject :: Nat) normalForms) == Just [terminate @Nat @a]
              | Some @a <- objects
              ]
          )
        expect "all maps on sizes 0 through 4" 126 (length forms)
        expect "bijection with the existing X/Y representation" expectedMaps (S.fromList (map modelKey forms))
        check "epi–mono factorisations agree with Simplex image factorisation" $
          and
            [ case (NF.epiMonoFactorization normalForms p, factorize (interpret p)) of
                (Just (NF.EpiMonoFactorization e m), expectedEpi@Objs :.: expectedMono) ->
                  (images (interpret e), images (interpret m)) == (images expectedEpi, images expectedMono)
                _ -> False
            | SomePath p <- forms
            ]
        check
          "composition changes the interpreted map"
          ( and
              [ interpret (KB.rewrite system g p) == generatorMap g . interpret p
              | SomePath @_ @b p <- forms
              , NF.Generator @c g <- generators
              , Just Refl <- [eqT @b @c]
              ]
          )
    , testProperty "epic and monic arrows agree with surjective and injective simplex maps" $
        check "incorrect cancellation result" $
          and
            [ let values = images (interpret p)
                  imageSize = S.size (S.fromList values)
              in NF.isEpi normalForms p == Just (toInteger imageSize == dimension @b)
                   && NF.isMono normalForms p == Just (imageSize == length values)
            | Some @a <- objects
            , Some @b <- objects
            , Just ps <- [NF.enumerate @a @b normalForms]
            , p <- ps
            ]
    ]
