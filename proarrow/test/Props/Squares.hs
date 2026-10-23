module Props.Squares (test) where

import Data.Functor.Compose (Compose (..))
import Data.Kind (Type)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Category.Instance.Bool (BOOL, Booleans (..))
import Proarrow.Category.Instance.Unit (Unit (..))
import Proarrow.Core ((:~>), type (+->))
import Proarrow.Functor qualified as F
import Proarrow.Limit.BinaryProduct (Product)
import Proarrow.Optic (ExOptic (..), Flip)
import Proarrow.Optic.Getter (GetterFl (..))
import Proarrow.Optic.Lens (LensFl)
import Proarrow.Path (Path (..))
import Proarrow.Profunctor.Corepresentable (Corep (..))
import Proarrow.Profunctor.Instance.Composition ((:.:) (..))
import Proarrow.Profunctor.Instance.Constant (Constant)
import Proarrow.Profunctor.Instance.Identity (Id (..))
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Instance.Terminal (TerminalProfunctor (..))
import Proarrow.Profunctor.Representable (Rep (..), Representable (..))
import Proarrow.Squares
  ( InputSquare
  , Sq (..)
  , fromTop
  , hArr
  , mkSquare
  , opticSquare
  , proSquare
  , runSquare
  , toBottom
  , vArr
  , (===)
  , (|||)
  )
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
    ]
