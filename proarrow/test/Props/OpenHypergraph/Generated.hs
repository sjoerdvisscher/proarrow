{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Interpret typed free diagrams directly in Mat Integer and read their open hypergraphs
-- back into TNET Int. Compare entries modulo the machine word size. The generator changes
-- boundaries only by typed composition, tensor and trace; it never builds raw node lists.
-- Three wires of dimensions two or three keep the independent dense reference small.
module Props.OpenHypergraph.Generated (test) where

import Data.Foldable (toList)
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Type.Equality ((:~:) (..))
import Data.Type.Nat (Nat2, Nat3)
import Test.Falsify (Gen, Property, testFailed)
import Test.Falsify qualified as F
import Test.Falsify.Generator (elem, oneof)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (Monoid, elem, fmap, id, mappend, mempty, (**), (.))
import Prelude qualified as P

import Proarrow.Category.Enriched.Thin (Member (..), memberIndex)
import Proarrow.Category.Instance.Bool (BOOL (..))
import Proarrow.Category.Instance.Discrete (DISCRETE (..))
import Proarrow.Category.Instance.Discrete qualified as Discrete
import Proarrow.Category.Instance.Free (FREE (..), Free, emb, fold)
import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Category.Instance.OpenHypergraph
  ( SIMPLIFY
  , Wires
  , Wiring
  , copyDiscard
  , frobenius
  , layered
  , permutations
  , prim1
  , simplify
  , tracedWith
  )
import Proarrow.Category.Instance.TensorNetwork (TNET (..))
import Proarrow.Category.Instance.TensorNetwork qualified as TNet
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor (..), SymMonoidal (..), UnitF, type (**!))
import Proarrow.Category.Monoidal.CompactClosed (CompactClosedStructures)
import Proarrow.Category.Monoidal.Hypergraph (traceHG)
import Proarrow.Category.Monoidal.Strictified (Strictified (..), type (++))
import Proarrow.Core (CAT, CategoryOf (..), Kind, Promonad (..), UN, obj, type (+->))
import Proarrow.Functor (FunctorForRep (..))
import Proarrow.Monoid (Comonoid (..), Monoid (..), Supplies)
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Representable (Rep)
import Proarrow.Testing (expect, genNamed)
import Props.Mat ()

type M2 :: MatK Integer
type M2 = M Nat2
type M3 :: MatK Integer
type M3 = M Nat3

type Dimension :: BOOL -> MatK Integer
type family Dimension a where
  Dimension FLS = M2
  Dimension TRU = M3

-- The discrete base has two object sorts, with independent endomorphisms and rectangular gates.
data Gate :: CAT (DISCRETE BOOL) where
  Gate :: forall a b. String -> Mat (Dimension a) (Dimension b) -> Gate (D a) (D b)

instance Show (Gate a b) where
  show (Gate name _) = name

data family Dense :: DISCRETE BOOL +-> MatK Integer
instance FunctorForRep Dense where
  type Dense @ a = Dimension (UN D a)
  fmap @a Discrete.Refl = case memberIndex @a of
    Here -> obj @M2
    There Here -> obj @M3

type NetworkDimension :: BOOL -> TNET Int
type family NetworkDimension a where
  NetworkDimension FLS = TN '[2]
  NetworkDimension TRU = TN '[3]

data family Graph :: DISCRETE BOOL +-> SIMPLIFY (TNET Int)
instance FunctorForRep Graph where
  type Graph @ a = Wires '[NetworkDimension (UN D a)]
  fmap @a Discrete.Refl = case memberIndex @a of
    Here -> obj @(Wires '[TN '[2]])
    There Here -> obj @(Wires '[TN '[3]])

denseGate :: Gate a b -> Dimension (UN D a) ~> Dimension (UN D b)
denseGate (Gate _ m) = m

networkGate :: forall a b. (Ob a, Ob b) => Gate a b -> NetworkDimension (UN D a) ~> NetworkDimension (UN D b)
networkGate g = case (memberIndex @a, memberIndex @b) of
  (Here, Here) -> TNet.fromEntries rows
  (Here, There Here) -> TNet.fromEntries rows
  (There Here, Here) -> TNet.fromEntries rows
  (There Here, There Here) -> TNet.fromEntries rows
  where
    rows :: [[Int]] = map (map fromInteger) (entries (denseGate g))

type Structures :: [Kind -> Constraint]
type Structures = CompactClosedStructures ++ '[Supplies Monoid, Supplies Comonoid]
type Diagram :: Kind
type Diagram = FREE Structures Gate

type A :: Diagram
type A = EMB (D FLS)
type B :: Diagram
type B = EMB (D TRU)

type Shape :: Diagram -> Type
data Shape a where
  UnitShape :: Shape UnitF
  TwoShape :: Shape A
  ThreeShape :: Shape B
  TensorShape :: (Ob a, Ob b) => Shape a -> Shape b -> Shape (a **! b)

data SomeDiagram where
  SomeDiagram :: Shape a -> Shape b -> Free a b -> SomeDiagram

instance Show SomeDiagram where
  show (SomeDiagram a b f) = showShape a ++ " -> " ++ showShape b ++ ": " ++ show f

showShape :: Shape a -> String
showShape UnitShape = "I"
showShape TwoShape = "2"
showShape ThreeShape = "3"
showShape (TensorShape a b) = "(" ++ showShape a ++ " ** " ++ showShape b ++ ")"

width :: Shape a -> Int
width UnitShape = 0
width TwoShape = 1
width ThreeShape = 1
width (TensorShape a b) = width a + width b

sameShape :: Shape a -> Shape b -> Maybe (a :~: b)
sameShape UnitShape UnitShape = Just Refl
sameShape TwoShape TwoShape = Just Refl
sameShape ThreeShape ThreeShape = Just Refl
sameShape (TensorShape a b) (TensorShape c d) = do
  Refl <- sameShape a c
  Refl <- sameShape b d
  pure Refl
sameShape _ _ = Nothing

data Fragment = Symmetric | Copying | TracedSymmetric | TracedCopying | Hypergraphs
  deriving (Eq)

copies :: Fragment -> Bool
copies Symmetric = False
copies TracedSymmetric = False
copies _ = True

traces :: Fragment -> Bool
traces Symmetric = False
traces Copying = False
traces _ = True

-- Each step is an existing Free morphism, not another syntax tree to interpret.
data Step a where
  Step :: Shape b -> Free a b -> Step a

genStep :: forall a. (Ob a) => Fragment -> NonEmpty SomeDiagram -> Int -> Shape a -> Gen (Step a)
genStep fragment gates capacity shape = oneof (pure (Step shape id) :| options)
  where
    options =
      [ pure (Step (TensorShape UnitShape shape) leftUnitorInv)
      , pure (Step (TensorShape shape UnitShape) rightUnitorInv)
      ]
        ++ [pure (Step target f) | SomeDiagram source target f <- toList gates, Just Refl <- [sameShape source shape]]
        ++ case shape of
          TensorShape a b ->
            [ pure (Step (TensorShape b a) swap)
            , do
                Step a' f@Objs <- genStep fragment gates (capacity - width b) a
                pure (Step (TensorShape a' b) (f ** obj))
            , do
                Step b' f@Objs <- genStep fragment gates (capacity - width a) b
                pure (Step (TensorShape a b') (obj ** f))
            ]
              ++ [pure (Step a mappend) | fragment == Hypergraphs, Just Refl <- [sameShape a b]]
              ++ case (a, b) of
                (UnitShape, _) -> [pure (Step b leftUnitor)]
                (_, UnitShape) -> [pure (Step a rightUnitor)]
                (TensorShape x y, _) -> [pure (Step (TensorShape x (TensorShape y b)) associator)]
                (_, TensorShape y z) -> [pure (Step (TensorShape (TensorShape a y) z) associatorInv)]
                _ -> []
          UnitShape
            | fragment == Hypergraphs
            , capacity > 0 ->
                [pure (Step TwoShape mempty), pure (Step ThreeShape mempty)]
          _ -> []
        ++ [pure (Step UnitShape counit) | copies fragment]
        ++ [pure (Step (TensorShape shape shape) comult) | copies fragment, 2 * width shape <= capacity]

genDiagram :: Fragment -> NonEmpty SomeDiagram -> Int -> Gen SomeDiagram
genDiagram fragment gates = grow
  where
    starts =
      [ SomeDiagram UnitShape UnitShape id
      , SomeDiagram TwoShape TwoShape id
      , SomeDiagram ThreeShape ThreeShape id
      , SomeDiagram (TensorShape TwoShape ThreeShape) (TensorShape TwoShape ThreeShape) id
      , SomeDiagram (TensorShape ThreeShape TwoShape) (TensorShape ThreeShape TwoShape) id
      ]
    grow 0 = oneof (elem gates :| [elem starts])
    grow n = do
      SomeDiagram a b f@Objs <- grow (n - 1)
      let extend = do
            Step c g <- genStep fragment gates 3 b
            pure (SomeDiagram a c (g . f))
          tensor =
            [ do
                SomeDiagram c d g@Objs <- elem gates
                left <- elem [False, True]
                pure $
                  if left
                    then SomeDiagram (TensorShape a c) (TensorShape b d) (f ** g)
                    else SomeDiagram (TensorShape c a) (TensorShape d b) (g ** f)
            | max (width a) (width b) < 3
            ]
          feedback = case (a, b) of
            (TensorShape u x, TensorShape v y)
              | traces fragment
              , width u == 1
              , Just Refl <- sameShape u v ->
                  [pure (SomeDiagram x y (traceHG f))]
            _ -> []
      oneof (extend :| (tensor ++ feedback))

primitives :: Property (NonEmpty SomeDiagram)
primitives = do
  f22 <- integerMatrix <$> genNamed @(Mat (M Nat2 :: MatK Int) (M Nat2)) "f22"
  g22 <- integerMatrix <$> genNamed @(Mat (M Nat2 :: MatK Int) (M Nat2)) "g22"
  f23 <- integerMatrix <$> genNamed @(Mat (M Nat2 :: MatK Int) (M Nat3)) "f23"
  f32 <- integerMatrix <$> genNamed @(Mat (M Nat3 :: MatK Int) (M Nat2)) "f32"
  f33 <- integerMatrix <$> genNamed @(Mat (M Nat3 :: MatK Int) (M Nat3)) "f33"
  g33 <- integerMatrix <$> genNamed @(Mat (M Nat3 :: MatK Int) (M Nat3)) "g33"
  pure
    [ SomeDiagram TwoShape TwoShape (emb (Gate @FLS @FLS "f22" f22))
    , SomeDiagram TwoShape TwoShape (emb (Gate @FLS @FLS "g22" g22))
    , SomeDiagram TwoShape ThreeShape (emb (Gate @FLS @TRU "f23" f23))
    , SomeDiagram ThreeShape TwoShape (emb (Gate @TRU @FLS "f32" f32))
    , SomeDiagram ThreeShape ThreeShape (emb (Gate @TRU @TRU "f33" f33))
    , SomeDiagram ThreeShape ThreeShape (emb (Gate @TRU @TRU "g33" g33))
    ]

-- Reuse the small integer generators, then compute in an unbounded ring.
integerMatrix :: Mat (M m :: MatK Int) (M n) -> Mat (M m :: MatK Integer) (M n)
integerMatrix (Mat rows) = Mat (P.fmap (P.fmap toInteger) rows)

entries :: Mat (a :: MatK Integer) b -> [[Integer]]
entries (Mat rows) = map toList (toList rows)

-- TNET varies the rightmost wire fastest; Mat's tensor varies the left factor fastest.
-- For each TNET boundary index, give the corresponding index of the dense reference.
basisOrder :: Shape a -> [Int]
basisOrder UnitShape = [0]
basisOrder TwoShape = [0, 1]
basisOrder ThreeShape = [0, 1, 2]
basisOrder (TensorShape a b) =
  let left = basisOrder a
  in [i + length left * j | i <- left, j <- basisOrder b]

compareReadBack :: [(String, Wiring (TNET Int))] -> SomeDiagram -> Property ()
compareReadBack readers diagram@(SomeDiagram a b f) = do
  let dense = entries (fold @Structures @(Rep Dense) denseGate f)
      expected :: [[Int]] = [[fromInteger (dense !! i !! j) | j <- basisOrder a] | i <- basisOrder b]
      graph = fold @Structures @(Rep Graph) (prim1 . networkGate) f
  mapM_
    ( \(name, wiring) -> case simplify wiring graph of
        Left err -> testFailed (name ++ ": " ++ err ++ "\n" ++ show diagram) :: Property ()
        Right (Str actual) -> expect (name ++ ": " ++ show diagram) expected (TNet.entries actual)
    )
    (readers ++ [("layered " ++ name, layered wiring) | (name, wiring) <- readers])

test :: TestTree
test =
  testGroup
    "generated diagrams"
    [ testProperty name $ do
        gates <- primitives
        size <- F.gen (elem [3 .. 6])
        diagram <- F.gen (genDiagram fragment gates size)
        compareReadBack [(name, wiring), ("hypergraph", other)] diagram
    | (name, fragment, wiring, other) <-
        [ ("symmetric monoidal", Symmetric, permutations, frobenius)
        , ("copy/discard", Copying, copyDiscard, frobenius)
        , ("traced symmetric monoidal", TracedSymmetric, tracedWith permutations, frobenius)
        , ("traced copy/discard", TracedCopying, tracedWith copyDiscard, frobenius)
        , ("hypergraph", Hypergraphs, frobenius, tracedWith frobenius)
        ]
    ]

-- For GHC 9.10
instance MonadFail Gen where
  fail = error
