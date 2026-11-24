{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A bounded path presentation for finite sets and functions. Extend the
-- simplicial generators by adjacent transpositions. Generate the short
-- relations involving swaps by grouping parallel words with the same table.
module Examples.KnuthBendix.FinSet (test, normalFormTables, normalFormMaps, table) where

import Control.Monad (forM_, replicateM)
import Data.Fin (Fin (..), toNatural, universe, weakenLeft1)
import Data.Kind (Type)
import Data.List (permutations, sort)
import Data.Map.Strict qualified as M
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat0, Nat1, Nat2, Nat3, Nat4)
import Data.Typeable (eqT)
import Data.Vec.Lazy qualified as V
import Examples.KnuthBendix.Simplex qualified as SX
import Test.Falsify (Property, testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (Word, id, (.))

import Proarrow.Category.Instance.FinSet (FinSet (..))
import Proarrow.Category.Instance.FinSet qualified as FS
import Proarrow.Category.Instance.Paths (EqGen (..), PATHS (..), Paths (..), pathLength)
import Proarrow.Category.Instance.Simplex (Forget, IsNat, Nat (..))
import Proarrow.Core (CAT, Promonad (..), UN)
import Proarrow.Functor qualified as F
import Proarrow.Object (SomeOb, SomeOf (..))
import Proarrow.Testing (expect)
import Proarrow.Tools.KnuthBendix qualified as KB
import Proarrow.Tools.KnuthBendix.NormalForms qualified as NF
import Proarrow.Tools.Laws (ProEquation ((:=:)))
import Proarrow.Tools.Laws qualified as Laws

type Generator :: CAT Nat
data Generator a b where
  Monotone :: SX.Generator a b -> Generator a b
  Swap :: forall n. (IsNat n) => Fin (S n) -> Generator (S (S n)) (S (S n))

instance EqGen Generator where
  eqGen (Monotone f) (Monotone g) = eqGen f g
  eqGen (Swap @n i) (Swap @m j) = case eqT @n @m of
    Just Refl | i == j -> Just Refl
    _ -> Nothing
  eqGen _ _ = Nothing

rank :: Generator a b -> (Int, Integer, Integer)
rank (Monotone g) = SX.rank g
rank (Swap @n i) = (2, size @(S (S n)), toInteger (toNatural i))

size :: forall n. (IsNat n) => Integer
size = toInteger (length (universe @n))

objects :: [SomeOb Nat]
objects = [Some @Nat0, Some @Nat1, Some @Nat2, Some @Nat3, Some @Nat4]

alphabet :: [NF.Generator Generator]
alphabet =
  [NF.Generator (Monotone g) | NF.Generator g <- SX.generators]
    ++ swaps @Nat0
    ++ swaps @Nat1
    ++ swaps @Nat2
  where
    swaps :: forall n. (IsNat n) => [NF.Generator Generator]
    swaps = [NF.Generator (Swap @n i) | i <- universe @(S n)]

generatorMap :: Generator a b -> FinSet (FS.FS a) (FS.FS b)
generatorMap (Monotone g@SX.Face{}) = FinSet (V.tabulate (F.fmap @Forget (SX.generatorMap g)))
generatorMap (Monotone g@SX.Degeneracy{}) = FinSet (V.tabulate (F.fmap @Forget (SX.generatorMap g)))
generatorMap (Swap i) = FinSet (V.tabulate swap)
  where
    left = weakenLeft1 i
    right = FS i
    swap x
      | x == left = right
      | x == right = left
      | otherwise = x

type Word :: Nat -> Nat -> Type
type Word a b = Paths (PTH a :: PATHS Generator) (PTH b)

interpret :: (IsNat a) => Word a b -> FinSet (FS.FS a) (FS.FS b)
interpret PNil = id
interpret (PCons g rest) = generatorMap g . interpret rest

table :: FinSet a b -> [Integer]
table (FinSet xs) = map (toInteger . toNatural) (V.toList xs)

normalFormTables :: forall a b. (IsNat a, IsNat b) => Either String [[Integer]]
normalFormTables = map table <$> normalFormMaps @a @b

normalFormMaps :: forall a b. (IsNat a, IsNat b) => Either String [FinSet (FS.FS a) (FS.FS b)]
normalFormMaps = do
  forms <- normalForms
  maybe (Left "undeclared FinSet endpoint") (Right . map interpret) (NF.enumerate @a @b forms)

liftPath :: Paths (a :: PATHS SX.Generator) b -> Word (UN PTH a) (UN PTH b)
liftPath PNil = PNil
liftPath (PCons g rest) = PCons (Monotone g) (liftPath rest)

mentionsSwap :: Word a b -> Bool
mentionsSwap PNil = False
mentionsSwap (PCons Monotone{} rest) = mentionsSwap rest
mentionsSwap (PCons Swap{} _) = True

localEquations :: forall a b. (IsNat a, IsNat b) => [Word a b] -> [KB.Equation Generator]
localEquations paths =
  [ w :=: representative
  | (key, w) <- wordsByTable
  , let representative = first M.! key
  , w /= representative
  , mentionsSwap w || mentionsSwap representative
  ]
  where
    wordsByTable = [(table (interpret w), w) | w <- paths]
    first = M.fromListWith (\_ earlier -> earlier) wordsByTable

equations :: NF.NormalForms Generator -> [KB.Equation Generator]
equations free =
  [Laws.withSides e (\l r -> liftPath l :=: liftPath r) | e <- SX.equations @Nat4]
    ++ concat
      [ localEquations (takeWhile ((<= 3) . pathLength) paths)
      | Some @a <- objects
      , Some @b <- objects
      , Just paths <- [NF.enumerate @a @b free]
      ]

test :: TestTree
test =
  testGroup
    "FinSet rewriting"
    [ testProperty "faces, degeneracies and swaps present all functions through size four" $ do
        forms <- either testFailed pure normalForms
        forM_ [(a, b) | a <- objects, b <- objects] (checkHomSet forms)
    , testProperty "discovers the product, coproduct and one-point gluing of two two-element sets" $ do
        forms <- either testFailed pure normalForms
        let coneTable :: NF.Cone Generator Nat2 Nat2 -> [(Integer, Integer)]
            coneTable (NF.Cone l r) = zip (table (interpret l)) (table (interpret r))
            coconeTable :: NF.Cocone Generator Nat2 Nat2 -> [Integer]
            coconeTable (NF.Cocone l r) = table (interpret l) ++ table (interpret r)
            point = PCons (Monotone (SX.Face @Nat1 (FS FZ))) PNil
        -- Every relabelling of the apex gives a different witness.
        expect
          "2 × 2 has all 24 labellings of the four pairs"
          (Just (sort (permutations [(0, 0), (0, 1), (1, 0), (1, 1)])))
          (sort . map coneTable <$> NF.binaryProducts @Nat2 @Nat2 forms)
        expect
          "2 + 2 has all 24 labellings of the disjoint union"
          (Just (sort (permutations [0, 1, 2, 3])))
          (sort . map coconeTable <$> NF.binaryCoproducts @Nat2 @Nat2 forms)
        expect
          "gluing the first points has all six labellings of the three-point pushout"
          (Just (sort [[shared, left, shared, right] | [shared, left, right] <- permutations [0, 1, 2]]))
          (sort . map coconeTable <$> NF.pushouts forms point point)
    ]

normalForms :: Either String (NF.NormalForms Generator)
normalForms = do
  free <- maybe (Left "free normal-form compilation failed") Right (NF.compile objects alphabet empty)
  case KB.completeWithOrder rank (KB.Limits 5000 1000000) (equations free) of
    completion@(KB.Complete _) ->
      maybe (Left "FinSet normal-form compilation failed") Right (NF.compile objects alphabet completion)
    KB.Incomplete reason _ _ -> Left (show reason)
  where
    empty = KB.completeWithOrder rank (KB.Limits 0 0) []

checkHomSet :: NF.NormalForms Generator -> (SomeOb Nat, SomeOb Nat) -> Property ()
checkHomSet forms (Some @a, Some @b) = do
  let label = show (size @a) ++ " → " ++ show (size @b)
      expected = replicateM (fromInteger (size @a)) (map (toInteger . toNatural) (universe @b))
  expect ("cardinality of " ++ label) (Just (NF.Finite (fromInteger (size @b ^ size @a)))) (NF.cardinality @a @b forms)
  expect
    ("one normal form per function " ++ label)
    (Just (sort expected))
    (sort . map (table . interpret) <$> NF.enumerate @a @b forms)
