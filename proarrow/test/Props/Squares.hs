module Props.Squares (test) where

import Data.Functor.Compose (Compose (..))
import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Adjunction qualified as Adj
import Proarrow.Category.Instance.Bool (BOOL, Booleans (..))
import Proarrow.Category.Instance.Coproduct (COPRODUCT)
import Proarrow.Category.Instance.Prof (Prof (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core ((:~>), type (+->))
import Proarrow.Functor qualified as F
import Proarrow.Limit.BinaryProduct (Product)
import Proarrow.Optic (ExOptic (..), Flip)
import Proarrow.Optic.Getter (GetterFl (..))
import Proarrow.Optic.Lens (LensFl)
import Proarrow.Path (Path (..), leftUnitor, rightUnitor)
import Proarrow.Profunctor.Corepresentable (Corep (..), Corepresentable (coindex))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Costar (Costar, unCostar, pattern Costar)
import Proarrow.Profunctor.Instance.HaskValue (HaskValue)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Ran qualified as Ran
import Proarrow.Profunctor.Instance.Rift qualified as Rift
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable
  ( CorepStar (..)
  , Rep (..)
  , RepCostar (..)
  , Representable (..)
  , mapCorepStar
  , unwrapCorepresentable
  , unwrapRepresentable
  , wrapCorepresentable
  , wrapRepresentable
  )
import Proarrow.Squares
  ( InputSquare
  , Sq (..)
  , fromTop
  , hArr
  , mapSq
  , mkSquare
  , opticSquare
  , proSquare
  , runSquare
  , toBottom
  , vArr
  , (===)
  , (|||)
  )
import Proarrow.Squares.Kan qualified as K
import Proarrow.Squares.Limit qualified as L
import Proarrow.Testing (expect, genNamed)
import Props.Hask ()

reverseList :: Star [] :~> Star []
reverseList (Star f) = Star (reverse . f)

dropFirst :: Star [] :~> Star []
dropFirst (Star f) = Star (drop 1 . f)

vertical :: Sq (Star [] ::: Nil) (Star [] ::: Nil) Nil Nil
vertical = vArr reverseList === vArr dropFirst

horizontal :: Sq (Star [] ::: Star [] ::: Nil) (Star [] ::: Star [] ::: Nil) Nil Nil
horizontal = vArr reverseList ||| vArr dropFirst

-- The two nested lists distinguish the first and second legs of the composed path.
input :: [Bool] -> (Star [] :.: Star []) () Bool
input xs = Star (const xs) :.: Star (\n -> [n, not n, False])

type Crossing = Sq (Star [] ::: Nil) (Star [] ::: Nil) (Star Maybe ::: Nil) (Star Maybe ::: Nil)

crossing :: Crossing
crossing = mkSquare (\(Star f) -> Star (traverse f))

-- The constructor exposes arbitrary arrows on both representable legs.
constructorCrossing :: Crossing
constructorCrossing = Sq (\(Star f :.: Star p) -> Star (traverse p . f) :.: Star id)

type NestedCrossing =
  Sq (Star [] ::: Nil) (Star [] ::: Nil) (Star Maybe ::: Star [] ::: Nil) (Star Maybe ::: Star [] ::: Nil)

nestedCrossing :: NestedCrossing
nestedCrossing = mkSquare (\(Star f) -> Star (traverse (traverse f)))

emptySquare :: Sq Nil Nil (Nil :: Path BOOL BOOL) Nil
emptySquare = mkSquare id

type ListEffect = Star (F.Prelude [])
type LensP = Rep (Product Bool)
type LensQ = Corep (Product Bool)

unpackData :: InputSquare LensP (Star ((,) Bool)) (Star [])
unpackData = mkSquare \(Id f) -> Rep (\(flag, a) -> (flag, [f a]))

rebuildData :: InputSquare LensQ (Star Maybe) (Star (Compose ((,) Bool) Maybe))
rebuildData = mkSquare \(Id f) -> Corep (\(flag, a) -> Compose (flag, f <$> a))

mixedInput :: InputSquare ListEffect (Star []) (Star Maybe)
mixedInput = mkSquare (\(Id f) -> Star (\xs -> F.Prelude (Nothing : map (Just . f) xs)))

type BoolShape :: () +-> Type
type BoolShape = Rep (Constant Bool)

-- Constant terminal weights recover binary products and coproducts.
type BinaryWeight :: COPRODUCT () () +-> ()
type BinaryWeight = TerminalProfunctor

type BinaryDiagram :: COPRODUCT () () +-> Type
type BinaryDiagram = Rep (Constant Bool)

type Reader :: Type +-> Type
type Reader = Star ((->) Bool)

type BinaryCoWeight :: () +-> COPRODUCT () ()
type BinaryCoWeight = TerminalProfunctor

type BinaryCoDiagram :: Type +-> COPRODUCT () ()
type BinaryCoDiagram = Corep (Constant Bool)

type ProductLeft :: Type +-> Type
type ProductLeft = Costar ((,) Bool)

identityLeg :: InputSquare Id BoolShape BoolShape
identityLeg = mkSquare \_ -> Id id

forgetLeg :: InputSquare TerminalProfunctor BoolShape BoolShape
forgetLeg = mkSquare (const TerminalProfunctor)

test :: TestTree
test =
  testGroup
    "Squares"
    [ testProperty "vertical composition applies the top square first" $ do
        xs <- genNamed @[Bool] "xs"
        case vertical of
          Sq n -> expect "bottom after top" (drop 1 (reverse xs)) (unStar (n (Star (const xs))) ())
    , testProperty "horizontal composition reads path legs right to left" $ do
        xs <- genNamed @[Bool] "xs"
        case horizontal of
          Sq n ->
            expect "left acts on the outer list" (reverse (map (\x -> [not x, False]) xs)) (index (n (input xs)) ())
    , testProperty "vertical composition of representable paths reads top to bottom" $ do
        xs <- genNamed @[Bool] "xs"
        case hArr reverseList === hArr dropFirst of
          Sq n ->
            expect
              "top acts on the inner list"
              (map (reverse . (\x -> [x, not x, False])) (drop 1 xs))
              (index (n (input xs)) ())
    , testProperty "horizontal companion bends recover the vertical identity" $ do
        xs <- genNamed @[Bool] "xs"
        case fromTop @(Star []) ||| toBottom @(Star []) of
          Sq n -> expect "straightened companion" xs (unStar (n (Star (const xs))) ())
    , testProperty "pointwise traversal agrees with traverse and the constructor" $ do
        xs <- genNamed @[Bool] "xs"
        let f b = b : xs
            values = [Nothing, Just False, Just True]
            run sq = map (unStar (runSquare sq (Star f))) values
        expect "traverse" (map (traverse f) values) (run crossing)
        expect "constructor" (run constructorCrossing) (run crossing)
    , testProperty "mapSq transforms a square with four nontrivial boundaries" $ do
        xs <- genNamed @[Bool] "xs"
        let transformed :: Crossing
            transformed =
              mapSq
                ( \(Prof n) -> Prof \p -> case n p of
                    Star effects :.: g -> Star (reverse . effects) :.: g
                )
                crossing
            f b = b : xs
            values = [Nothing, Just False, Just True]
        expect
          "reversed traversal results"
          (map (reverse . traverse f) values)
          (map (unStar (runSquare transformed (Star f))) values)
    , testProperty "mkSquare . runSquare preserves the constructor payload" $ do
        xs <- genNamed @[Bool] "xs"
        let rebuilt :: Crossing
            rebuilt = mkSquare (runSquare constructorCrossing)
            values = [Nothing, Just False, Just True]
            payload :: (Star Maybe :.: Star []) (Maybe Bool) Bool
            payload = Star (fmap not) :.: Star (: xs)
        case (constructorCrossing, rebuilt) of
          (Sq original, Sq restored) ->
            expect "arbitrary representable input" (map (index (original payload)) values) (map (index (restored payload)) values)
    , testProperty "pointwise conversion handles composed representable paths" $ do
        xs <- genNamed @[Bool] "xs"
        let f b = b : xs
            values = [[], [Nothing], map Just xs, [Just False, Nothing, Just True]]
        expect
          "nested traversal"
          (map (traverse (traverse f)) values)
          (map (unStar (runSquare nestedCrossing (Star f))) values)
    , testProperty "pointwise conversion handles composed profunctor paths" $ do
        xs <- genNamed @[Bool] "xs"
        let n = index (runSquare (crossing ||| crossing) (input xs))
        expect "no data" [[Nothing]] (n Nothing)
        expect "data" (map (map Just . (\x -> [x, not x, False])) xs) (n (Just ()))
    , testProperty "pointwise conversion handles empty paths in a non-Hask category" $
        case runSquare emptySquare (Id F2T) of
          Id f -> expect "identity" F2T f
    , testProperty "proSquare absorbs a residual pair around the effect" $ do
        xs <- genNamed @[Bool] "xs"
        flag <- genNamed @Bool "flag"
        let lensCrossing = proSquare @LensFl @ListEffect @LensP @LensQ
            effect = Star (\b -> F.Prelude (b : xs))
            run = F.unPrelude . unStar (runSquare lensCrossing (Rep id :.: effect :.: Corep id))
        expect "residual" (map (flag,) (True : xs)) (run (flag, True))
    , testProperty "opticSquare composes different read and write shapes" $ do
        flag <- genNamed @Bool "flag"
        value <- genNamed @Bool "value"
        let program = opticSquare @LensFl @ListEffect @LensP @LensQ unpackData rebuildData mixedInput
            run = map getCompose . F.unPrelude . unStar (runSquare program (Id not))
        expect "mixed optic" [(flag, Nothing), (flag, Just (not value))] (run (flag, value))
    , testProperty "opticSquare accepts a right witness without corepresentability" $
        let focus :: InputSquare (ExOptic GetterFl Bool Bool) BoolShape BoolShape
            focus = mkSquare (\(Id Unit) -> ExOptic (Id not) (Id id))
            program = opticSquare @GetterFl identityLeg forgetLeg focus
        in case runSquare program (Id Unit) of
             ExOptic @p @q left _ -> expect "getter" False (getP @p @q left True)
    , testProperty "opticSquare accepts a left witness without representability" $
        let focus :: InputSquare (ExOptic (Flip GetterFl) Bool Bool) BoolShape BoolShape
            focus = mkSquare (\(Id Unit) -> ExOptic (Id id) (Id not))
            program = opticSquare @(Flip GetterFl) forgetLeg identityLeg focus
        in case runSquare program (Id Unit) of
             ExOptic @p @q _ right -> expect "review" True (getP @q @p right False)
    , testProperty "Ran square factorization satisfies evaluation and uniqueness" $ do
        xs <- genNamed @[Bool] "xs"
        let cone :: Sq (Id ::: Star [] ::: Nil) (Star [] ::: Nil) Nil Nil
            cone = Sq rightUnitor
            factored = K.ranUniv cone
            rebuilt = K.ranUniv (K.ran @Id @(Star []))
            value :: Star [] Bool Bool
            value = Star (const xs)
        case (factored, rebuilt, K.ran @Id @(Star [])) of
          (Sq u, Sq v, Sq ev) -> do
            expect "evaluation" (map not xs) (unStar (ev (u value :.: Id not)) False)
            expect "uniqueness" (map not xs) (unStar (Ran.runRan (Id not) (v (u value))) False)
    , testProperty "Rift square factorization satisfies evaluation and uniqueness" $ do
        xs <- genNamed @[Bool] "xs"
        let cone :: Sq (Star [] ::: Id ::: Nil) (Star [] ::: Nil) Nil Nil
            cone = Sq leftUnitor
            value :: Star [] Bool Bool
            value = Star (: xs)
        case (K.riftUniv cone, K.riftUniv (K.rift @Id @(Star [])), K.rift @Id @(Star [])) of
          (Sq u, Sq v, Sq ev) -> do
            expect "evaluation" (True : xs) (unStar (ev (Id not :.: u value)) False)
            expect "uniqueness" (True : xs) (unStar (Rift.runRift (Id not) (v (u value))) False)
    , testProperty "pointwise Ran agrees with limits and factors cones" $ do
        xs <- genNamed @[Bool] "xs"
        let cone :: Sq (Id ::: Nil) Nil (Star [] ::: Nil) (Star [] ::: Nil)
            cone = Sq rightUnitor
            value :: Star [] Bool Bool
            value = Star (const xs)
            kanCone :: Sq Nil Nil (Id ::: Star [] ::: Nil) (Star [] ::: Nil)
            kanCone = Sq rightUnitor
        case (K.pwRanUniv kanCone, L.limitUniv @Id @Type cone) of
          (Sq u, Sq v) -> do
            expect "factorization" (map not xs) (unStar (Ran.runRan (Id not) (u value)) False)
            expect "limit factorization" xs (unStar (v value) False)
            expect "pointwise evaluation" (map not xs) (unId (runSquare (K.pwRan @Id @(Star [])) (Id not)) xs)
            expect "limit evaluation" (map not xs) (unId (runSquare (L.limit @Id @Type @(Star [])) (Id not)) xs)
    , testProperty "pointwise Lan agrees with colimits and factors cocones" $ do
        xs <- genNamed @[Bool] "xs"
        let cocone :: Sq (Id ::: Nil) Nil (CorepStar (Costar []) ::: Nil) (CorepStar (Costar []) ::: Nil)
            cocone = K.corepSquare leftUnitor
            kanCocone
              :: Sq Nil Nil (CorepStar (Costar []) ::: Nil) (CorepStar Id ::: CorepStar (Costar []) ::: Nil)
            kanCocone = Sq (\g -> g :.: CorepStar id)
        expect
          "mate roundtrip"
          (any not xs)
          (unCostar (K.corepSquareInv cocone (Id not :.: Costar or)) xs)
        expect
          "horizontal mate roundtrip"
          (any not xs)
          (unCostar (K.corepComposeSquareInv kanCocone (Id not :.: Costar or)) xs)
        expect "factorization" xs (unId (runSquare (K.pwLanUniv kanCocone) (Id id)) xs)
        expect "colimit factorization" xs (unId (runSquare (L.colimitUniv @Id @Type cocone) (Id id)) xs)
        expect "pointwise evaluation" (map not xs) (unId (runSquare (K.pwLan @Id @(Costar [])) (Id not)) xs)
        expect "colimit evaluation" (map not xs) (unId (runSquare (L.colimit @Id @Type @(Costar [])) (Id not)) xs)
    , testProperty "right adjoint preservation of products agrees with the profunctor proof and is invertible" $ do
        fFalse <- genNamed @Bool "f False"
        fTrue <- genNamed @Bool "f True"
        gFalse <- genNamed @Bool "g False"
        gTrue <- genNamed @Bool "g True"
        let f b = if b then fTrue else fFalse
            g b = if b then gTrue else gFalse
            points = [False, True]
            preserve = L.rightAdjointPreservesLimits @BinaryWeight @Reader @BinaryDiagram
            inverse = L.rightAdjointPreservesLimitsInv @BinaryWeight @Reader @BinaryDiagram
            forward = unId (runSquare preserve (Id Unit))
            reference = unId (runSquare (hArr (Adj.rightAdjointPreservesLimits @BinaryWeight @Reader @BinaryDiagram)) (Id Unit))
            (restoredF, restoredG) = unId (runSquare (preserve ||| inverse) (Id Unit)) (f, g)
            h b = (g b, f (not b))
        expect "product comparison" (map (\b -> (f b, g b)) points) (map (forward (f, g)) points)
        expect "profunctor proof" (map (reference (f, g)) points) (map (forward (f, g)) points)
        expect "left roundtrip" (map f points, map g points) (map restoredF points, map restoredG points)
        expect "right roundtrip" (map h points) (map (unId (runSquare (inverse ||| preserve) (Id Unit)) h) points)
    , testProperty "the canonical limit comparison also works for a functor that does not preserve products" $ do
        rows <- genNamed @[(Bool, Bool)] "rows"
        let comparison = L.rightAdjointPreservesLimitsInv @BinaryWeight @(Star []) @BinaryDiagram
        expect "list of pairs to pair of lists" (unzip rows) (unId (runSquare comparison (Id Unit)) rows)
    , testProperty "left adjoint preservation of coproducts agrees with the profunctor proof and is invertible" $ do
        flag <- genNamed @Bool "flag"
        value <- genNamed @(Either Bool Bool) "value"
        let preserve = L.leftAdjointPreservesColimits @BinaryCoWeight @ProductLeft @BinaryCoDiagram
            inverse = L.leftAdjointPreservesColimitsInv @BinaryCoWeight @ProductLeft @BinaryCoDiagram
            forward = unId (runSquare preserve (Id Unit))
            reference =
              unId
                ( runSquare
                    (hArr (unProf (mapCorepStar (Prof (Adj.leftAdjointPreservesColimits @ProductLeft @BinaryCoDiagram @BinaryCoWeight)))))
                    (Id Unit)
                )
            distribute (b, Left x) = Left (b, x)
            distribute (b, Right x) = Right (b, x)
            inputValue = (flag, value)
            outputValue = distribute inputValue
        expect "coproduct comparison" outputValue (forward inputValue)
        expect "profunctor proof" (reference inputValue) (forward inputValue)
        expect "left roundtrip" inputValue (unId (runSquare (preserve ||| inverse) (Id Unit)) inputValue)
        expect "right roundtrip" outputValue (unId (runSquare (inverse ||| preserve) (Id Unit)) outputValue)
    , testProperty "the canonical colimit comparison also works for a functor that does not preserve coproducts" $ do
        value <- genNamed @(Either [Bool] [Bool]) "value"
        let comparison = L.leftAdjointPreservesColimitsInv @BinaryCoWeight @(Costar []) @BinaryCoDiagram
        expect
          "sum of lists to list of sums"
          (either (map Left) (map Right) value)
          (unId (runSquare comparison (Id Unit)) value)
    , testProperty "left adjoints preserve copowers with a non-corepresentable weight" $ do
        flag <- genNamed @Bool "functor parameter"
        weight <- genNamed @Bool "weight parameter"
        value <- genNamed @Bool "value"
        let preserve = L.leftAdjointPreservesColimits @(HaskValue Bool :: () +-> ()) @ProductLeft @(Corep (Constant Bool))
            inverse = L.leftAdjointPreservesColimitsInv @(HaskValue Bool :: () +-> ()) @ProductLeft @(Corep (Constant Bool))
            inputValue = (flag, (weight, value))
        expect "copower comparison" (weight, (flag, value)) (unId (runSquare preserve (Id Unit)) inputValue)
        expect "roundtrip" inputValue (unId (runSquare (preserve ||| inverse) (Id Unit)) inputValue)
    , testProperty "representable wrapper cancellations are inverse in both directions" $ do
        xs <- genNamed @[Bool] "xs"
        let value :: Star [] Bool Bool
            value = Star (: xs)
            wrapped :: CorepStar (RepCostar (Star [])) Bool Bool
            wrapped = CorepStar (: xs)
        expect "original encoding" (True : xs) (unStar (unwrapRepresentable (wrapRepresentable value)) True)
        expect "double encoding" (True : xs) (index (wrapRepresentable (unwrapRepresentable wrapped)) True)
    , testProperty "corepresentable wrapper cancellations are inverse in both directions" $ do
        xs <- genNamed @[Bool] "xs"
        let value :: Costar [] Bool Bool
            value = Costar or
            wrapped :: RepCostar (CorepStar (Costar [])) Bool Bool
            wrapped = RepCostar or
        expect "original encoding" (or xs) (unCostar (unwrapCorepresentable (wrapCorepresentable value)) xs)
        expect "double encoding" (or xs) (coindex (wrapCorepresentable (unwrapCorepresentable wrapped)) xs)
    ]
