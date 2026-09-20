{-# LANGUAGE AllowAmbiguousTypes #-}

-- | The examples that ship with the @vitrea@ library (Mario Román and Bartosz Milewski,
-- /Profunctor optics: a categorical update/), ported to proarrow's optics: lenses and a prism over
-- records, a type-changing lens, an algebraic lens and a kaleidoscope over (a slice of) the iris
-- data set, monadic lenses as ordinary lenses in a Kleisli category, and a traversal composed with
-- a prism and a lens.
module Examples.Vitrea (test) where

import Data.Char (toUpper)
import Data.Function (on)
import Data.List (minimumBy)
import Data.Maybe (fromMaybe)
import Data.Type.Nat (Nat4)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude hiding (Applicative (..), Functor (..), id, map, (.))

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..), arr)
import Proarrow.Category.Monoidal.Applicative (Applicative (..))
import Proarrow.Core (Promonad (..))
import Proarrow.Functor (Functor (..))
import Proarrow.Optic (convert)
import Proarrow.Optic.Action (ClassifyingLens, classifyingLens, (.?))
import Proarrow.Optic.Kaleidoscope (Kaleidoscope', cotraverseOf, kaleidoscopeOf)
import Proarrow.Optic.PowerGrate (PowerGrate', powerGrate, powerGrateOf)
import Proarrow.Optics
  ( Lens
  , Lens'
  , MonoidalLens
  , Prism'
  , Traversal
  , foldMapOf
  , lens
  , monLens
  , over
  , prism
  , review
  , set
  , traversed
  , view
  , (%)
  , (^?)
  )
import Proarrow.Profunctor.Instance.Costar (unCostar, pattern Costar)
import Proarrow.Profunctor.Instance.Star (Star, unStar, pattern Star)
import Proarrow.Profunctor.Representable (RepCostar (..))
import Props.Optic.Hask (assertEq)

-- * Example 1: lenses and prisms

data Address = Address
  { street' :: String
  , city' :: String
  , country' :: String
  }
  deriving (Show, Eq)

data Person = Person
  { name' :: String
  , home' :: Address
  }
  deriving (Show, Eq)

sherlock :: Person
sherlock =
  Person
    { name' = "Sherlock Holmes"
    , home' = Address{street' = "221b Baker Street", city' = "London", country' = "UK"}
    }

home :: Lens' Person Address
home = lens home' (\(p, a) -> p{home' = a})

street :: Lens' Address String
street = lens street' (\(a, s) -> a{street' = s})

city :: Lens' Address String
city = lens city' (\(a, c) -> a{city' = c})

-- | Parse an address from @"street, city, country"@, or fail with the original string.
asAddress :: Prism' String Address
asAddress = prism buildAddress matchAddress
  where
    buildAddress (Address s c r) = s ++ ", " ++ c ++ ", " ++ r
    matchAddress a = case splitOn ", " a of
      [s, c, r] -> Right (Address s c r)
      _ -> Left a

splitOn :: String -> String -> [String]
splitOn sep = go
  where
    n = length sep
    go s = case breakOn s of
      (h, Nothing) -> [h]
      (h, Just rest) -> h : go rest
    breakOn [] = ([], Nothing)
    breakOn s@(c : cs)
      | take n s == sep = ([], Just (drop n s))
      | otherwise = let (h, r) = breakOn cs in (c : h, r)

place :: String
place = "221b Baker St, London, UK"

-- * Example 1.2: a type-changing lens (the clock is an 'Int' so the tests stay pure)

data Timestamped a = Timestamped
  { created' :: Int
  , modified' :: Int
  , contents' :: a
  }
  deriving (Show, Eq)

contents :: Lens (Timestamped a) (Timestamped b) a b
contents = lens contents' (\(x, b) -> x{contents' = b})

-- * Example 2: an algebraic lens and a kaleidoscope over the iris data set

data Species = Setosa | Versicolor | Virginica deriving (Show, Eq)

data Measurements = Measurements
  { sepalLe :: Float
  , sepalWi :: Float
  , petalLe :: Float
  , petalWi :: Float
  }
  deriving (Show, Eq)

data Flower = Flower
  { measurements :: Measurements
  , species :: Species
  }
  deriving (Show, Eq)

-- | Classify a new set of measurements by the species of its nearest neighbour in a list of flowers:
-- an algebraic lens for the list monad, whose @put@ sees the whole list rather than one flower.
measure :: ClassifyingLens (Star []) Flower Flower Measurements Measurements
measure = classifyingLens measurements (uncurry learn)
  where
    distance :: Measurements -> Measurements -> Float
    distance (Measurements a b c d) (Measurements x y z w) = sqrt (sum (map (** 2) ([a - x, b - y, c - z, d - w] :: [Float])))
    learn l m = Flower m (species (minimumBy (compare `on` (distance m . measurements)) l))

-- | The four measurements as a power grate, so that any way of aggregating a list of
-- 'Float's aggregates a list of 'Measurements' field by field.
aggregate :: PowerGrate' Measurements Float
aggregate =
  powerGrate @Nat4
    (\(Measurements a b c d) -> (a, (b, (c, (d, ())))))
    (\(a, (b, (c, (d, ())))) -> Measurements a b c d)

-- | Distribute a list aggregator through the kaleidoscope, at the carrier @Costar []@.
aggregateWith :: ([Float] -> Float) -> [Measurements] -> Measurements
aggregateWith = unCostar . powerGrateOf aggregate . Costar

-- | Classify the /aggregate/ of a list of flowers: the classifying lens composed with the kaleidoscope
-- is a kaleidoscope again (a product by a monoid is applicative), run at the aggregating
-- carrier @Costar []@ (vitrea's @iris & measure . aggregate >- mean@).
classifyAggregate :: ([Float] -> Float) -> [Flower] -> Flower
classifyAggregate = unCostar . kaleidoscopeOf measureAggregate . Costar

-- | The same composite, stored at its named flavor: Román's kaleidoscope.
measureAggregate :: Kaleidoscope' Flower Float
measureAggregate = convert (measure % aggregate)

-- | The kaleidoscope is also a cotraversal: pass a finite 'Cotraversable' carrier through it,
-- here @Maybe a -> b@, i.e. @RepCostar (Star Maybe)@.
classifyOptional :: (Maybe Float -> Float) -> Maybe Flower -> Flower
classifyOptional f = unRepCostar (cotraverseOf measureAggregate (RepCostar @_ @(Star Maybe) f))

mean :: [Float] -> Float
mean l = sum l / fromIntegral (length l)

setosa1 :: Flower
setosa1 = Flower (Measurements 5.1 3.5 1.4 0.2) Setosa

iris :: [Flower]
iris =
  [ setosa1
  , Flower (Measurements 4.9 3.0 1.4 0.2) Setosa
  , Flower (Measurements 4.7 3.2 1.3 0.2) Setosa
  , Flower (Measurements 5.4 3.9 1.7 0.4) Setosa
  , Flower (Measurements 4.4 2.9 1.4 0.2) Setosa
  , Flower (Measurements 7.0 3.2 4.7 1.4) Versicolor
  , Flower (Measurements 6.4 3.2 4.5 1.5) Versicolor
  , Flower (Measurements 5.5 2.3 4.0 1.3) Versicolor
  , Flower (Measurements 4.9 2.4 3.3 1.0) Versicolor
  , Flower (Measurements 5.0 2.0 3.5 1.0) Versicolor
  , Flower (Measurements 6.3 3.3 6.0 2.5) Virginica
  , Flower (Measurements 5.8 2.7 5.1 1.9) Virginica
  , Flower (Measurements 7.1 3.0 5.9 2.1) Virginica
  , Flower (Measurements 4.9 2.5 4.5 1.7) Virginica
  , Flower (Measurements 7.7 3.8 6.7 2.2) Virginica
  ]

-- * Example 3: monadic lenses are lenses in a Kleisli category

-- | A counter monad standing in for the clock: 'tick' returns the current time and advances it.
newtype Clock a = Clock {runClock :: Int -> (a, Int)}

instance Functor Clock where
  map f (Clock g) = Clock (\t -> let (a, t') = g t in (f a, t'))
instance Applicative Clock where
  pure a () = Clock (a (),)
  liftA2 h (Clock f, Clock g) = Clock (\t -> let (a, t') = f t; (b, t'') = g t' in (h (a, b), t''))
instance Promonad (Star Clock) where
  id = Star \a -> Clock (a,)
  Star f . Star g = Star \a -> Clock (\t -> let (b, t') = runClock (g a) t in let (c, t'') = runClock (f b) t' in (c, t''))

tick :: Clock Int
tick = Clock (\t -> (t, t + 1))

-- | Run a Kleisli arrow of @m@ on a plain value.
runK :: forall m a b. Kleisli (KL a :: KLEISLI (Star m)) (KL b) -> a -> m b
runK k = unStar (unKleisli k)

-- | A monadic lens over 'Clock': viewing is pure, updating also stamps the time.
--
-- This is a 'MonoidalLens', not a 'Lens'. The Kleisli category of a monad has coproducts but not
-- products -- @'fst' . (f '&&&' g)@ would run both effects where the law allows only @f@\'s -- so
-- the monadic lenses of the paper live over the Kleisli /tensor/, with a comonoidal residual,
-- rather than over a product. Here the residual is the whole record.
stamp :: forall a b. MonoidalLens (KL (Timestamped a) :: KLEISLI (Star Clock)) (KL (Timestamped b)) (KL a) (KL b)
stamp =
  monLens @(KL (Timestamped a))
    (arr (\x -> (x, contents' x)))
    (Kleisli (Star (\(x, b) -> map (\t -> x{contents' = b, modified' = t}) tick)))

-- | A writer-like monad, for a lens that logs its updates.
newtype Log a = Log {runLog :: ([String], a)}

instance Functor Log where
  map f (Log (w, a)) = Log (w, f a)
instance Applicative Log where
  pure a () = Log ([], a ())
  liftA2 f (Log (w, a), Log (w', b)) = Log (w ++ w', f (a, b))
instance Promonad (Star Log) where
  id = Star (Log . ([],))
  Star f . Star g = Star \a -> let Log (w, b) = g a in let Log (w', c) = f b in Log (w ++ w', c)

newtype Box a = Box {openBox :: a} deriving (Show, Eq)

box :: forall a b. (Show b) => MonoidalLens (KL (Box a) :: KLEISLI (Star Log)) (KL (Box b)) (KL a) (KL b)
box =
  monLens @(KL (Box a))
    (arr (\x -> (x, openBox x)))
    (Kleisli (Star (\(_, b) -> Log (["[box]: contents changed to " ++ show b ++ "."], Box b))))

-- * Example 4: traversals

each :: Traversal [a] [b] a b
each = traversed @(Star [])

uppercase :: String -> String
uppercase = map toUpper

places :: [String]
places =
  [ "43 Adlington Rd, Wilmslow, United Kingdom"
  , "26 Westcott Rd, Princeton, USA"
  , "St James's Square, London, United Kingdom"
  ]

test :: TestTree
test =
  testGroup
    "Vitrea examples"
    [ testProperty "view a composed lens" $ assertEq (view (home % street) sherlock) "221b Baker Street"
    , testProperty "set a composed lens" $
        assertEq (set (home % street) "221b Baker St" sherlock) sherlock{home' = (home' sherlock){street' = "221b Baker St"}}
    , testProperty "over a composed lens" $ assertEq (view (home % city) (over (home % city) uppercase sherlock)) "LONDON"
    , testProperty "preview a prism" $ assertEq (place ^? asAddress) (Just (Address "221b Baker St" "London" "UK"))
    , testProperty "preview a prism that fails" $ assertEq ("nowhere" ^? asAddress) Nothing
    , testProperty "review a prism" $ assertEq (review asAddress (Address "221b Baker St" "London" "UK")) place
    , testProperty "over a prism composed with a lens" $
        assertEq (over (asAddress % city) uppercase place) "221b Baker St, LONDON, UK"
    , testProperty "type-changing lens" $
        assertEq (over contents length (Timestamped 0 1 "What is the answer?")) (Timestamped 0 1 19)
    , testProperty "algebraic lens classifies by nearest neighbour (setosa)" $
        assertEq (species ((measure .? Measurements 4.8 3.1 1.5 0.1) iris)) Setosa
    , testProperty "algebraic lens classifies by nearest neighbour (virginica)" $
        assertEq (species ((measure .? Measurements 7.2 3.1 6.1 2.3) iris)) Virginica
    , testProperty "algebraic lens keeps the measurements it classified" $
        assertEq (measurements ((measure .? Measurements 6.1 2.9 4.2 1.3) iris)) (Measurements 6.1 2.9 4.2 1.3)
    , testProperty "kaleidoscope aggregates field by field" $
        let ms = map measurements iris
        in assertEq
             (aggregateWith mean ms)
             (Measurements (mean (map sepalLe ms)) (mean (map sepalWi ms)) (mean (map petalLe ms)) (mean (map petalWi ms)))
    , testProperty "kaleidoscope with maximum" $
        let ms = map measurements iris
        in assertEq (aggregateWith maximum ms) (Measurements 7.7 3.9 6.7 2.5)
    , testProperty "classifying lens composed with kaleidoscope classifies the mean" $
        assertEq (classifyAggregate mean iris) ((measure .? aggregateWith mean (map measurements iris)) iris)
    , testProperty "the composite is a cotraversal: classify an optional flower" $
        assertEq (species (classifyOptional (fromMaybe 0) (Just setosa1))) Setosa
    , testProperty "algebraic lens is a lens: view" $ assertEq (view measure setosa1) (Measurements 5.1 3.5 1.4 0.2)
    , testProperty "algebraic lens is a lens: over" $
        assertEq (species (over measure id setosa1)) Setosa
    , testProperty "monadic lens: view is pure" $
        assertEq (runClock (runK (view stamp) (Timestamped 0 0 "What is the answer?")) 7) ("What is the answer?", 7)
    , testProperty "monadic lens: update stamps the time" $
        assertEq
          (runClock (runK (over stamp (arr (const "42"))) (Timestamped 0 0 "What is the answer?")) 7)
          (Timestamped 0 7 "42", 8)
    , testProperty "monadic lens: update logs" $
        assertEq (runLog (runK (over box (arr (+ 1))) (Box (41 :: Int)))) (["[box]: contents changed to 42."], Box 42)
    , testProperty "traversal over a list" $ assertEq (over each length ["a", "bb", "ccc"]) [1, 2, 3 :: Int]
    , testProperty "traversal composed with prism and lens" $
        assertEq
          (over (each % asAddress % city) uppercase places)
          [ "43 Adlington Rd, WILMSLOW, United Kingdom"
          , "26 Westcott Rd, PRINCETON, USA"
          , "St James's Square, LONDON, United Kingdom"
          ]
    , testProperty "fold through traversal, prism and lens" $
        assertEq
          (foldMapOf (each % asAddress % street) (: []) places)
          ["43 Adlington Rd", "26 Westcott Rd", "St James's Square"]
    ]
