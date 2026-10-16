{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoOverloadedLists #-}

-- | Two optics composed by graph substitution, following §10 of Wilson and Zanasi,
-- <https://arxiv.org/abs/2305.01041 Data-Parallel Algorithms for String Diagrams>.
-- Each source wire becomes a forward/backward pair. A generator becomes two boxes connected by
-- its residual. Graph composition connects the forward boxes in source order and the backward
-- boxes in reverse order. Moving the external backward wires gives an ordinary computation from
-- @(a⁺, c⁻)@ to @(c⁺, a⁻)@, with both residuals computed once and used by their backward boxes.
module Examples.OpticDiagrams (test, sourcePicture, encodedPicture, compositionPicture, derivativeSourcePicture, derivativePicture) where

import Data.Either (isLeft)
import Data.Kind (Type)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as M
import Data.Vector.Storable qualified as SV
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (id, mempty, (**), (.))

import Proarrow.Category.Instance.DecoratedCospan (DECCOSPAN (..), DecCospan (..))
import Proarrow.Category.Instance.Diff qualified as Diff
import Proarrow.Category.Instance.FinHask (FinHask (..))
import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.OpenHypergraph
  ( Box (..)
  , Boxes (..)
  , OPENHG
  , Port (..)
  , SomeArrow
  , SomeHypergraph (..)
  , SomeSort
  , WireSorts
  , Wires
  , box
  , frobenius
  , isomorphic
  , openHypergraph
  , readBack
  , sameSort
  , someArrow
  , sortList
  , substituteWith
  , unsafeOpenHypergraph
  )
import Proarrow.Category.Instance.Sub (Sub (..))
import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor, SymMonoidal (..), Tensor)
import Proarrow.Category.Monoidal.Action (ActionAt)
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CAT, CategoryOf (..), Promonad (..), obj)
import Proarrow.Functor qualified as Functor
import Proarrow.Monoid (Comonoid (..), Monoid (..))
import Proarrow.Object (SomeOf (..), pattern Objs)
import Proarrow.Optic (Optic, Prostrong, iso, legs2prof)
import Proarrow.Optic.Action (ActFl, runMonoidalOptic)
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (Rep (..))
import Proarrow.Testing (check, expect, genNamed)
import Proarrow.Tools.Diagrams.Svg (SVG (..), Svg (..), W (Wire), node, render)
import Proarrow.Tools.Optic (OPTICS, optic, opticLegs, runOptics)
import Proarrow.Tools.SMC (SYN (F, Not, (:**)), annihilate, lift, produce, toSMC, (**), (-<))
import Proarrow.Tools.SMC qualified as SMC
import Props.Mat ()

data Gate = First | Second deriving (Eq, Show)
data Leg = Forward Gate | Backward Gate deriving (Eq, Show)

type A = S '[Wire "a"]
type B = S '[Wire "b"]
type C = S '[Wire "c"]
type AF = S '[Wire "a⁺"]
type AB = S '[Wire "a⁻"]
type BF = S '[Wire "b⁺"]
type BB = S '[Wire "b⁻"]
type CF = S '[Wire "c⁺"]
type CB = S '[Wire "c⁻"]
type MF = S '[Wire "m_f"]
type MG = S '[Wire "m_g"]
type Target = OPENHG SVG Leg

type Encoded = (Wires '[AF, AB] :: Target) ~> Wires '[CF, CB]
type Running = (Wires '[AF, CB] :: Target) ~> Wires '[CF, AB]

source :: (Wires '[A] :: OPENHG SVG Gate) ~> Wires '[C]
source = box @_ @'[B] @'[C] Second . box @_ @'[A] @'[B] First

objectMap :: SomeSort SVG -> [SomeSort SVG]
objectMap s
  | sameSort s (Some @A) = sortList @_ @'[AF, AB]
  | sameSort s (Some @B) = sortList @_ @'[BF, BB]
  | sameSort s (Some @C) = sortList @_ @'[CF, CB]
  | otherwise = error "objectMap: outside the example's signature"

-- The backward box's output meets the left boundary, and its input meets the right boundary.
generatorMap :: Gate -> SomeHypergraph SVG Leg
generatorMap First = opticBox @AF @AB @BF @BB @MF First
generatorMap Second = opticBox @BF @BB @CF @CB @MG Second

opticBox
  :: forall (a :: SVG) (da :: SVG) (b :: SVG) (db :: SVG) (m :: SVG)
   . (Ob a, Ob da, Ob b, Ob db, Ob m)
  => Gate -> SomeHypergraph SVG Leg
opticBox gate =
  SomeHypergraph $
    unsafeOpenHypergraph @Leg @'[a, da] @'[b, db]
      (sortList @_ @'[a, da, b, db, m])
      [0, 1]
      [2, 3]
      [Box (Forward gate) [0] [2, 4], Box (Backward gate) [4, 3] [1]]

encoded :: Either String Encoded
encoded = do
  SomeHypergraph graph <- substituteWith objectMap generatorMap source
  let (nodes, ins, outs, boxes) = parts graph
  openHypergraph nodes ins outs boxes

-- Backward wires have negative types; SMC supplies their duality bends.
running :: Either String Running
running = do
  graph <- encoded
  pure $ toSMC @(F (Wires '[AF]) :** Not (F (Wires '[CB]))) @(F (Wires '[CF]) :** Not (F (Wires '[AB]))) \(a, dc) -> SMC.do
    (da, da') <- produce @(F (Wires '[AB]))
    (c, dc') <- graph -< (a, da)
    () <- annihilate dc dc'
    c ** da'

parts :: forall l a b. (a :: OPENHG SVG l) ~> b -> ([SomeSort SVG], [Int], [Int], [Box l Int])
parts (DecCospan @c (Sub (FinHask l)) (Sub (FinHask r)) (Boxes boxes)) =
  (sortList @_ @(WireSorts (DC c)), fmap unPort (M.elems l), fmap unPort (M.elems r), fmap (fmap unPort) boxes)
  where
    unPort (Port i) = i

-- An independent description of the composite optic, with one residual node for each generator.
expected :: Running
expected =
  unsafeOpenHypergraph
    (sortList @_ @'[AF, AB, BF, BB, CF, CB, MF, MG])
    [0, 5]
    [4, 1]
    [ Box (Forward First) [0] [2, 6]
    , Box (Forward Second) [2] [4, 7]
    , Box (Backward Second) [7, 5] [3]
    , Box (Backward First) [6, 3] [1]
    ]

-- The same computation written as an SMC program, with the backward pass in reverse order.
scheduled :: Running
scheduled =
  composePasses @_ @(Wires '[AF]) @(Wires '[BF]) @(Wires '[CF]) @(Wires '[AB]) @(Wires '[BB]) @(Wires '[CB])
    @(Wires '[MF])
    @(Wires '[MG])
    (box @Leg @'[AF] @'[BF, MF] (Forward First))
    (box @Leg @'[BF] @'[CF, MG] (Forward Second))
    (box @Leg @'[MF, BB] @'[AB] (Backward First))
    (box @Leg @'[MG, CB] @'[BB] (Backward Second))

-- This program runs in the symbolic graph and in the writer used to count numerical evaluations.
composePasses
  :: forall {k} (p :: CAT k) (a :: k) (b :: k) (c :: k) (da :: k) (db :: k) (dc :: k) (m :: k) (n :: k)
   . (SymMonoidal k, Promonad p, MonoidalProfunctor p, Ob c, Ob dc, Ob m, Ob n)
  => p a (b ** m) -> p b (c ** n) -> p (m ** db) da -> p (n ** dc) db -> p (a ** dc) (c ** da)
composePasses forward1@Objs forward2@Objs backward1@Objs backward2@Objs =
  SMC.proc @(F a :** F dc) @(F c :** F da) \(a, dc) -> SMC.do
    (b, m) <- lift @(F a) @(F b :** F m) forward1 a
    (c, n) <- lift @(F b) @(F c :** F n) forward2 b
    db <- backward2 -< (n, dc)
    da <- backward1 -< (m, db)
    c ** da

-- | The source function of the derivative example: @x ↦ sin (x²)@.
derivativeSourcePicture :: String
derivativeSourcePicture = render (node @'[Wire "b"] @'[Wire "c"] "sin" . node @'[Wire "a"] @'[Wire "b"] "square")

-- | The substituted graph with concrete forward and reverse-derivative primitives.
-- The square saves x; the sine saves cos(x²). Neither forward operation is repeated backward.
derivativePicture :: Either String String
derivativePicture = running >>= drawGraph derivativeLeg

derivativeLeg :: Leg -> SomeArrow SVG
derivativeLeg = drawLeg \case
  Forward First -> "z = x²; save x"
  Forward Second -> "y = sin z; save cos z"
  Backward First -> "dx = 2x · dz"
  Backward Second -> "dz = cos z · dy"

runDerivative :: (Double, Double) -> ([String], (Double, Double))
runDerivative =
  Functor.unPrelude
    . unStar
      ( composePasses
          (Star (\x -> Functor.Prelude (["square"], (x * x, x))))
          (Star (\z -> Functor.Prelude (["sin"], (sin z, cos z))))
          (Star (\(x, dz) -> Functor.Prelude (["square backward"], 2 * x * dz)))
          (Star (\(cosZ, dy) -> Functor.Prelude (["sin backward"], cosZ * dy)))
      )

-- The source program uses ordinary SMC composition. Its optic primitives supply the residuals;
-- runOptics builds and substitutes the graph, then reads the numerical computation back.
derivativeFunction :: Either String ((Double, Double) -> (Double, Double))
derivativeFunction = runOptics derivativeProgram

type Number = Wires '[ '(Double, Double)] :: OPTICS Type

square :: Number ~> Number
square = opticLegs @Double (\x -> (x, x * x)) (\(x, dy) -> 2 * x * dy)

sine :: Number ~> Number
sine = opticLegs @Double (\x -> (cos x, sin x)) (uncurry (*))

parallel :: Number ** Number ~> Number ** Number
parallel = toSMC @(F Number :** F Number) \(x, y) -> SMC.do
  x' <- square -< x
  y' <- sine -< y
  x' ** y'

type Logged = KLEISLI (Star (Functor.Prelude ((,) [String])))
type LoggedWire = Wires '[ '(KL Double, KL Double)] :: OPTICS Logged

loggedProgram :: LoggedWire ~> LoggedWire
loggedProgram = toSMC @(F LoggedWire) \x -> SMC.do
  y <- f -< x
  g -< y
  where
    logged :: String -> (a -> b) -> (KL a :: Logged) ~> KL b
    logged name f' = Kleisli (Star (\a -> Functor.Prelude ([name], f' a)))
    f, g :: LoggedWire ~> LoggedWire
    f = opticLegs @(KL Double) (logged "square" (\x -> (x, x * x))) (logged "square backward" (\(x, dy) -> 2 * x * dy))
    g = opticLegs @(KL Double) (logged "sin" (\x -> (cos x, sin x))) (logged "sin backward" (uncurry (*)))

derivativeProgram :: Number ~> Number
derivativeProgram = toSMC @(F Number) \x -> SMC.do
  z <- square -< x
  sine -< z

reference :: Diff.Diff (Diff.DF '[1]) (Diff.DF '[1])
reference = Diff.pointwise @1 sin cos . Diff.pointwise @1 (\x -> x * x) (2 *)

close :: Double -> Double -> Bool
close expectedValue actual = abs (expectedValue - actual) <= 1e-8 * max 1 (abs expectedValue)

interpret :: Leg -> SomeArrow SVG
interpret = drawLeg \case
  Forward First -> "f forward"
  Forward Second -> "g forward"
  Backward First -> "f backward"
  Backward Second -> "g backward"

drawLeg :: (Leg -> String) -> Leg -> SomeArrow SVG
drawLeg name leg@(Forward First) = someArrow @'[AF] @'[BF, MF] (Str (node @'[Wire "a⁺"] @'[Wire "b⁺", Wire "m_f"] (name leg)))
drawLeg name leg@(Forward Second) = someArrow @'[BF] @'[CF, MG] (Str (node @'[Wire "b⁺"] @'[Wire "c⁺", Wire "m_g"] (name leg)))
drawLeg name leg@(Backward First) = someArrow @'[MF, BB] @'[AB] (Str (node @'[Wire "m_f", Wire "b⁻"] @'[Wire "a⁻"] (name leg)))
drawLeg name leg@(Backward Second) = someArrow @'[MG, CB] @'[BB] (Str (node @'[Wire "m_g", Wire "c⁻"] @'[Wire "b⁻"] (name leg)))

sourcePicture :: String
sourcePicture = render (node @'[Wire "b"] @'[Wire "c"] "g" . node @'[Wire "a"] @'[Wire "b"] "f")

encodedPicture :: Either String String
encodedPicture = encoded >>= drawGraph interpret

compositionPicture :: Either String String
compositionPicture = running >>= drawGraph interpret

drawGraph :: (Leg -> SomeArrow SVG) -> (a :: Target) ~> b -> Either String String
drawGraph draw graph = do
  Str picture@Svg{} <- readBack frobenius draw graph
  pure (render picture)

test :: TestTree
test =
  testGroup
    "Optic diagrams"
    [ testProperty "substitution agrees with the hand-built composite" $
        either testFailed (check "different wiring" . isomorphic expected) running
    , testProperty "substitution agrees with the SMC computation" $
        either testFailed (check "different wiring" . isomorphic scheduled) running
    , testProperty "compiling optics agrees with extracting the composite's legs" $ do
        let first :: Optic (Prostrong (ActFl Tensor)) (Wires '[AF] :: Target) (Wires '[AB]) (Wires '[BF]) (Wires '[BB])
            first =
              legs2prof @(ActFl Tensor)
                ( Rep @_ @(ActionAt Tensor (Wires '[MF]))
                    (swap @Target @(Wires '[BF]) @(Wires '[MF]) . box @Leg @'[AF] @'[BF, MF] (Forward First))
                )
                (Corep @_ @(ActionAt Tensor (Wires '[MF])) (box @Leg @'[MF, BB] @'[AB] (Backward First)))
            second :: Optic (Prostrong (ActFl Tensor)) (Wires '[BF] :: Target) (Wires '[BB]) (Wires '[CF]) (Wires '[CB])
            second =
              legs2prof @(ActFl Tensor)
                ( Rep @_ @(ActionAt Tensor (Wires '[MG]))
                    (swap @Target @(Wires '[CF]) @(Wires '[MG]) . box @Leg @'[BF] @'[CF, MG] (Forward Second))
                )
                (Corep @_ @(ActionAt Tensor (Wires '[MG])) (box @Leg @'[MG, CB] @'[BB] (Backward Second)))
            graph =
              optic @_ @'[ '(Wires '[BF], Wires '[BB])] @'[ '(Wires '[CF], Wires '[CB])] second
                . optic @_ @'[ '(Wires '[AF], Wires '[AB])] @'[ '(Wires '[BF], Wires '[BB])] first
            connected :: Running
            connected = runMonoidalOptic (first . second)
        compiled <- either testFailed pure (runOptics graph)
        check "different wiring" (isomorphic connected compiled)
    , testProperty "sin(x²) computes its value and reverse derivative" $ do
        i <- genNamed @Int "input"
        j <- genNamed @Int "cotangent"
        function <- either testFailed pure derivativeFunction
        let x = fromIntegral (i `mod` 25 - 12) / 4
            dy = fromIntegral (j `mod` 9 - 4) / 2
            (calls, (y, dx)) = runDerivative (x, dy)
            (graphY, graphDx) = function (x, dy)
            point = Diff.Vector (SV.singleton x)
            seed = Diff.Vector (SV.singleton dy)
            (referenceY, pullback) = Diff.run reference point
        expect
          "each primitive once, backward in reverse order"
          ["square", "sin", "sin backward", "square backward"]
          calls
        check "graph forward agrees with the SMC schedule" (close y graphY)
        check "graph backward agrees with the SMC schedule" (close dx graphDx)
        check "forward value" (close (sin (x * x)) y)
        check "chain rule" (close (2 * x * cos (x * x) * dy) dx)
        check "Diff forward" (close (SV.head (Diff.coordinates referenceY)) y)
        check "Diff backward" (close (SV.head (Diff.coordinates (pullback seed))) dx)
        let eps = 1e-6
            f t = sin (t * t)
            finiteDifference = (f (x + eps) - f (x - eps)) / (2 * eps)
        check "finite differences" (close (finiteDifference * dy) dx)
    , testProperty "derivative graph keeps one of each primitive" $
        either
          testFailed
          ( \graph ->
              let (_, _, _, boxes) = parts graph
                  legs = [Forward First, Backward First, Forward Second, Backward Second]
              in do
                   expect
                     "one of each primitive"
                     [1, 1, 1, 1]
                     [length (filter ((== leg) . label) boxes) | leg <- legs]
          )
          running
    , testProperty "source picture draws both generators" $
        check "missing source generators" (all (`isInfixOf` sourcePicture) [">f<", ">g<"])
    , testProperty "encoded picture draws the forward and backward boxes" $
        either
          testFailed
          ( \picture -> check "missing encoded boxes" (all (`isInfixOf` picture) ["f forward", "g forward", "f backward", "g backward"])
          )
          encodedPicture
    , testProperty "derivative source picture draws square and sine" $
        check "missing derivative generators" (all (`isInfixOf` derivativeSourcePicture) ["square", "sin"])
    , testProperty "derivative picture draws values, residuals and pullbacks" $
        either
          testFailed
          ( \picture ->
              check
                "missing derivative boxes"
                (all (`isInfixOf` picture) ["x²; save x", "sin z; save cos z", "2x · dz", "cos z · dy"])
          )
          derivativePicture
    , testProperty "both forward and backward boxes are drawn" $
        either
          testFailed
          (\picture -> check "missing boxes" (all (`isInfixOf` picture) ["f forward", "g forward", "f backward", "g backward"]))
          compositionPicture
    , testProperty "parallel SMC primitives keep both backward wires in order" $ do
        i <- genNamed @Int "x"
        j <- genNamed @Int "z"
        f <- either testFailed pure (runOptics parallel)
        let x = fromIntegral (i `mod` 7 - 3)
            z = fromIntegral (j `mod` 7 - 3)
            ((y, w), (dx, dz)) = f ((x, z), (2, 3))
        expect "forward square" (x * x) y
        expect "forward sine" (sin z) w
        expect "backward square" (4 * x) dx
        expect "backward sine" (3 * cos z) dz
    , testProperty "compiled computation executes each primitive once" $ do
        Kleisli f <- either testFailed pure (runOptics loggedProgram)
        let (calls, (y, dx)) = Functor.unPrelude (unStar f (2, 3))
        expect "order and multiplicity" ["square", "sin", "sin backward", "square backward"] calls
        expect "value" (sin 4) y
        check "derivative" (abs (12 * cos 4 - dx) < 1e-12)
    , testProperty "multi-output primitive supplies an SMC tuple pattern" $ do
        let duplicate :: Number ~> Number ** Number
            duplicate = opticLegs @() (\x -> ((), (x, x))) (\((), (dx, dy)) -> dx + dy)
            program = toSMC @(F Number) \x -> SMC.do
              (u, v) <- duplicate -< x
              a <- square -< u
              b <- sine -< v
              a ** b
        f <- either testFailed pure (runOptics program)
        let ((y, z), dx) = f (2, (1, 1))
        expect "two forward results" (4, sin 2) (y, z)
        expect "cotangents are added by the duplication optic" (4 + cos 2) dx
    , testProperty "nullary primitive has an empty source boundary" $ do
        let constant :: (Wires '[] :: OPTICS Type) ~> Wires '[ '(Int, Int)]
            constant = opticLegs @() (\() -> ((), 7)) (\((), _) -> ())
        f <- either testFailed pure (runOptics constant)
        expect "constant" (7, ()) (f ((), 5))
    , testProperty "multi-input primitive folds its source ports" $ do
        let multiply :: Number ** Number ~> Number
            multiply = opticLegs @(Double, Double) (\(x, y) -> ((x, y), x * y)) (\((x, y), dz) -> (y * dz, x * dz))
        f <- either testFailed pure (runOptics multiply)
        expect "product rule" (6, (12, 8)) (f ((2, 3), 4))
    , testProperty "primitive can have an empty target boundary" $ do
        let finish :: (Wires '[ '(Int, Int)] :: OPTICS Type) ~> Wires '[]
            finish = opticLegs @Int (,()) (\(x, ()) -> x + 1)
        f <- either testFailed pure (runOptics finish)
        expect "saved residual" ((), 9) (f (8, ()))
    , testProperty "different forward, backward and residual types" $ do
        let primitive :: (Wires '[ '(Int, String)] :: OPTICS Type) ~> Wires '[ '(Double, Char)]
            primitive = opticLegs @Bool (\n -> (even n, fromIntegral n / 2)) (\(evenN, c) -> replicate (if evenN then 1 else 2) c)
        f <- either testFailed pure (runOptics primitive)
        expect "even residual" (4, "x") (f (8, 'x'))
        expect "odd residual" (4.5, "yy") (f (9, 'y'))
    , testProperty "existing optic encoding" $ do
        let o :: Optic (Prostrong (ActFl Tensor)) Int String Double Char
            o = iso fromIntegral (replicate 2)
        f <- either testFailed pure (runOptics (optic @_ @'[ '(Int, String)] @'[ '(Double, Char)] o))
        expect "iso legs" (7, "zz") (f (7, 'z'))
    , testProperty "permutation reverses the backward boundary permutation" $ do
        let graph = swap @(OPTICS Type) @(Wires '[ '(Int, Bool)]) @(Wires '[ '(Double, Char)])
        f <- either testFailed pure (runOptics graph)
        expect "mixed permutation" ((2.5, 7), (True, 'z')) (f ((7, 2.5), ('z', True)))
    , testProperty "identity needs no primitives" $ do
        f <- either testFailed pure (runOptics (obj @Number))
        expect "identity" (3, 7) (f (3, 7))
    , testProperty "empty boundaries fold to the unit" $ do
        f <- either testFailed pure (runOptics (obj @(Wires '[] :: OPTICS Type)))
        expect "unit" ((), ()) (f ((), ()))
    , testProperty "copying requires stronger target wiring" $
        check "copy accepted" (isLeft (runOptics (comult @Number)))
    , testProperty "discarding requires stronger target wiring" $
        check "discard accepted" (isLeft (runOptics (counit @Number)))
    , testProperty "isolated feedback requires a trace" $
        check "feedback accepted" (isLeft (runOptics (counit @Number . mempty @Number)))
    ]
