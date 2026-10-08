{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Open hypergraphs with wires sorted by 'Int' and 'Bool'. Equality is 'isomorphic', so the laws
-- hold up to renaming nodes and reordering boxes, and the examples check that terms equal by the
-- Frobenius laws give isomorphic hypergraphs and that others do not.
module Props.OpenHypergraph (test) where

import Control.Monad (replicateM)
import Data.Kind (Type)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as M
import Data.Type.Nat (Nat2, Nat3)
import Data.Universe.Class (Finite (..))
import Test.Falsify (Property, testFailed)
import Test.Falsify.Generator (elem)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (elem, id, mappend, mempty, (**), (.))

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.FinHask (FINHASK (..), FinHask (..))
import Proarrow.Category.Instance.Mat (Mat (..), MatK (..))
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , Boxes (..)
  , OPENHG
  , SomeArrow
  , Sorted
  , WireSorts
  , Wires
  , box
  , isomorphic
  , prim
  , readBack
  , simplify
  , someArrow
  , sortList
  , sortOf
  )
import Proarrow.Category.Instance.Sub (SUBCAT (..), Sub (..))
import Proarrow.Category.Monoidal (MonoidalProfunctor (..))
import Proarrow.Category.Monoidal.Hypergraph (cap, cup)
import Proarrow.Category.Monoidal.Strictified (Fold, Strictified (..), singleton)
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), UN, obj)
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Testing
  ( SomeOf (..)
  , Testable (..)
  , TestableProfunctor
  , TestableType (..)
  , TestingEqShow (..)
  , check
  , genNamed
  , genSomeDef
  , pattern GenNonEmpty
  )
import Proarrow.Testing.Laws
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)
import Proarrow.Tools.Einsum (einsum)
import Proarrow.Tools.SMC.Examples (hadamardT, matMulT, traceIdxT)
import Props.Mat ()
import Props.SMC (name)

type OH = OPENHG Type String

-- | One wire of each sort.
type I = Wires '[Int] :: OH

type B = Wires '[Bool] :: OH

test :: TestTree
test =
  testGroup
    "Open hypergraphs"
    [ testCategory @OH
    , testDagger @OH
    , testMonoidal_ @OH
    , testSymMonoidal_ @OH
    , testClosed_ @OH
    , testDialogue_ @OH
    , testStarAutonomous_ @OH
    , testIsoMix_ @OH
    , testCompactClosed_ @OH
    , testCopyDiscard_ @OH
    , testHypergraph_ @OH
    , testGroup
        "the Frobenius laws"
        [ testProperty "matrix multiplication in index notation is composition" $
            check "not isomorphic" (isomorphic (matMulT f h) (h . f))
        , testProperty "the trace in index notation is the cap after the cup" $
            check "not isomorphic" (isomorphic (traceIdxT g) (cap @I . (g ** obj @I) . cup @I))
        , testProperty "the entrywise product in index notation is mappend after the two after comult" $
            check "not isomorphic" (isomorphic (hadamardT f f') (mappend @B . (f ** f') . comult @I))
        , testProperty "speciality: copying then merging is the identity" $
            check "not isomorphic" (isomorphic (mappend @I . comult @I) id)
        , testProperty "a closed loop is not the empty diagram" $
            check "isomorphic" (not (isomorphic (counit @I . mempty @I) id))
        , testProperty "closed loops of different sorts differ" $
            check "isomorphic" (not (isomorphic (counit @I . mempty @I) (counit @B . mempty @B)))
        , testProperty "composition is not commutative" $
            check "isomorphic" (not (isomorphic (g . g') (g' . g)))
        , testProperty "einsum ij,jk is composition" $
            check "not isomorphic" (isomorphic (unStr (einsum @"ij,jk" (name f) (name h))) (unStr (name (h . f))))
        ]
    , testGroup
        "read-back in Mat Int"
        [ testProperty "matrix multiplication in index notation reads back as composition (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M3 ~> M2) "g"
            let Str m = simplify (matMulT (prim (singleton fm)) (prim (singleton gm)))
            check "differs from g . f" (unMat m == unMat (gm . fm))
        , testProperty "the trace reads back as the trace (3)" $ do
            gm <- genNamed @(M3 ~> M3) "g"
            m <- readBackOr (\_ -> someArrow (singleton gm)) (traceIdxT (box @_ @'[M3] @'[M3] "g"))
            check "differs" (unMat m == unMat (traceIdxT gm))
        , testProperty "the entrywise product reads back as the entrywise product (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M2 ~> M3) "g"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton gm)
            m <- readBackOr interp (hadamardT (box @_ @'[M2] @'[M3] "f") (box @_ @'[M2] @'[M3] "g"))
            check "differs" (unMat m == unMat (hadamardT fm gm))
        , testProperty "einsum ij,jk reads back as the name of the composite (2, 3)" $ do
            fm <- genNamed @(M2 ~> M3) "f"
            gm <- genNamed @(M3 ~> M2) "g"
            let interp x = if x == "f" then someArrow (singleton fm) else someArrow (singleton gm)
            m <-
              readBackOr
                interp
                (unStr (einsum @"ij,jk" (name (box @String @'[M2] @'[M3] "f")) (name (box @String @'[M3] @'[M2] "g"))))
            check "differs" (unMat m == unMat ((obj @M2 ** (gm . fm)) . cup @M2))
        , testProperty "a closed loop reads back as the dimension (3)" $ do
            m <- readBackOr (\_ -> error "no boxes") (counit @(Wires '[M3] :: OM) . mempty @(Wires '[M3]))
            check "not 3" (unMat m == unMat (counit @M3 . mempty @M3))
        ]
    , testGroup
        "read-back in SVG"
        [ testProperty "matrix multiplication in index notation reads back with no points" $ do
            let d = node @'[Wire "A"] @'[Wire "A"] "f"
                t = matMulT (box @_ @'[A] @'[A] "f") (box @_ @'[A] @'[A] "f") :: Wires '[A] ~> (Wires '[A] :: OPENHG SVG String)
            case readBack (\_ -> someArrow (singleton d)) t of
              Right (Str r) -> check "points are drawn" (points (render r) == 0)
              Left e -> testFailed e
        ]
    ]
  where
    points = length . filter ("<circle" `List.isPrefixOf`) . List.tails
    f = box @_ @'[Int] @'[Bool] "f"
    f' = box @_ @'[Int] @'[Bool] "f'"
    h = box @_ @'[Bool] @'[Int] "h"
    g = box @_ @'[Int] @'[Int] "g"
    g' = box @_ @'[Int] @'[Int] "g'"

type M2 = M Nat2 :: MatK Int
type M3 = M Nat3 :: MatK Int
type OM = OPENHG (MatK Int) String
type A = S '[Wire "A"]

-- | The read-back in Mat Int as a matrix, failing the property if it fails.
readBackOr
  :: forall a b
   . (String -> SomeArrow (MatK Int))
  -> (a :: OM) ~> b
  -> Property (Fold (WireSorts a) ~> Fold (WireSorts b))
readBackOr interp t = case readBack interp t of
  Right (Str m) -> pure m
  Left e -> testFailed e

instance Testable OH where
  showOb @a = "Wires " ++ show (sortList @Type @(WireSorts a))
  genSome =
    genSomeDef
      @'[ Wires '[]
        , Wires '[Int]
        , Wires '[Int, Bool]
        , Wires '[Bool, Bool, Int]
        , Wires '[Bool, Int, Int]
        ]

instance (Ob a, Ob b) => TestingEqShow (DecCospan a (b :: OH)) where
  eqP x y = pure (isomorphic x y)
  showP (DecCospan (Sub (FinHask l)) (Sub (FinHask r)) (Boxes bs)) =
    "DecCospan " ++ show l ++ " " ++ show r ++ " " ++ show bs

-- | A random apex from the palette, legs into it that keep the sorts of the ports, and up to two
-- boxes on its nodes.
instance (Ob a, Ob b) => TestableType (DecCospan a (b :: OH)) where
  gen = GenNonEmpty loop
    where
      loop = do
        c <- genSome @OH
        case c of
          Some @(DC (SUB (FH n))) -> do
            let nodesOfSort x = [y | y <- universeF @n, sortOf @Type @(FH n) y == x]
                leg :: forall p. (Sorted Type (FH p)) => Maybe [(p, NonEmpty n)]
                leg = traverse (\x -> case nodesOfSort (sortOf @Type @(FH p) x) of [] -> Nothing; y : ys -> Just (x, y :| ys)) universeF
            case (leg @(UN FH (UN SUB (UN DC a))), leg @(UN FH (UN SUB (UN DC b)))) of
              (Just la, Just lb) -> do
                l <- traverse (\(x, ys) -> (x,) <$> elem ys) la
                r <- traverse (\(x, ys) -> (x,) <$> elem ys) lb
                bs <- case universeF @n of
                  [] -> pure []
                  n0 : ns -> do
                    k <- elem [0 .. 2]
                    replicateM k do
                      x <- elem ["f", "g"]
                      ni <- elem [0 .. 2]
                      no <- elem [0 .. 2]
                      Box x <$> replicateM ni (elem (n0 :| ns)) <*> replicateM no (elem (n0 :| ns))
                pure (DecCospan (Sub (FinHask (M.fromList l))) (Sub (FinHask (M.fromList r))) (Boxes bs))
              _ -> loop

instance TestableProfunctor (DecCospan :: CAT OH)
