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
module Examples.SimplexRewrite (test, Generator (..), equations, system, completedRules) where

import Data.Fin (Fin (..), absurd, toNatural, universe, weakenLeft1)
import Data.Map.Strict qualified as M
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
import Proarrow.Core (CAT, Promonad (..), UN)
import Proarrow.Functor qualified as F
import Proarrow.Object (SomeOf (..))
import Proarrow.Testing (check, expect)
import Proarrow.Tools.KnuthBendix qualified as KB
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

objects :: [SomeOf IsNat]
objects = [Some @Nat0, Some @Nat1, Some @Nat2, Some @Nat3, Some @Nat4]

data SomeGenerator where
  SomeGenerator :: forall a b. (IsNat a, IsNat b) => Generator a b -> SomeGenerator

generators :: [SomeGenerator]
generators = concatMap atSize objects
  where
    atSize :: SomeOf IsNat -> [SomeGenerator]
    atSize (Some @n) =
      [SomeGenerator (Face @n i) | dimension @n < 4, i <- universe @(S n)]
        ++ [SomeGenerator (Degeneracy @n i) | dimension @n + 2 <= 4, i <- universe @(S n)]

data SomePath where
  SomePath :: forall a b. (IsNat a, IsNat b) => Paths (PTH a :: PATHS Generator) (PTH b) -> SomePath

wordKey :: SomePath -> (Integer, Integer, String)
wordKey (SomePath @a @b p) = (dimension @a, dimension @b, show p)

modelKey :: SomePath -> (Integer, Integer, String)
modelKey (SomePath @a @b p) = (dimension @a, dimension @b, show (interpret p))

extensions :: SomePath -> [SomePath]
extensions (SomePath @_ @b p) =
  [ SomePath (KB.rewrite system g p)
  | SomeGenerator @c g <- generators
  , Just Refl <- [eqT @b @c]
  ]

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

-- Enumerate normal paths by closing identities under every generator. A faulty
-- presentation cannot make the test search unboundedly for extra normal forms.
normalForms :: Either String [SomePath]
normalForms = go M.empty [SomePath (PNil :: Paths (PTH n) (PTH n)) | Some @n <- objects]
  where
    go seen [] = Right (M.elems seen)
    go seen (p : pending)
      | M.member (wordKey p) seen = go seen pending
      | M.size seen >= S.size expectedMaps = Left "more normal forms than monotone maps"
      | otherwise = go (M.insert (wordKey p) p seen) (extensions p ++ pending)

test :: TestTree
test =
  testGroup
    "Simplex face/degeneracy rewriting"
    [ testProperty "Mathlib's simplicial identities hold in Simplex" $ do
        check "a generator has the wrong monotone map" (all (\(SomeGenerator g) -> generatorCorrect g) generators)
        expect "no relations below size 2" 0 (length (equations @Nat0) + length (equations @Nat1))
        check
          "an incorrectly indexed relation"
          (all (\e -> Laws.withSides e (\l r -> interpret l == interpret r)) (equations @Nat5))
    , testProperty "completion gives one normal form for every monotone map" $ do
        case completion of
          KB.Complete _ -> pure ()
          KB.Incomplete reason _ _ -> testFailed (show reason)
        forms <- either testFailed pure normalForms
        expect "all maps on sizes 0 through 4" 126 (length forms)
        expect "bijection with the existing X/Y representation" expectedMaps (S.fromList (map modelKey forms))
        check
          "composition changes the interpreted map"
          ( and
              [ interpret (KB.rewrite system g p) == generatorMap g . interpret p
              | SomePath @_ @b p <- forms
              , SomeGenerator @c g <- generators
              , Just Refl <- [eqT @b @c]
              ]
          )
    ]
