-- | Exact, finite, normalised probability distributions. Construction is total:
-- 'weighted' rejects negative weights and zero total mass, and 'condition'
-- returns 'Nothing' for an impossible event. Internal branches need not have
-- distinct values, so mapping and binding require no ordering constraint.
-- 'probabilities', equality, ordering, and display combine repeated outcomes.
module Examples.OpenGames.Probability
  ( Distribution
  , ProbabilityError (..)
  , weighted
  , uniform
  , probabilities
  , collect
  , weightedValues
  , expectation
  , probability
  , condition
  ) where

import Control.Monad (ap)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Prelude

-- Deterministic structural arrows need no probability multiplication or
-- singleton lists. Payloads and weighted branch lists remain lazy.
data Distribution a = Certain ~a | Distribution ~[(a, Rational)]

fromBranches :: [(a, Rational)] -> Distribution a
fromBranches [(x, 1)] = Certain x
fromBranches xs = Distribution xs

data ProbabilityError = NegativeWeight | ZeroMass deriving (Eq, Show)

-- | Normalise nonnegative weights. Zero-weight branches are removed.
weighted :: [(a, Rational)] -> Either ProbabilityError (Distribution a)
weighted xs
  | any ((< 0) . snd) xs = Left NegativeWeight
  | total == 0 = Left ZeroMass
  | otherwise = Right (fromBranches [(x, p / total) | (x, p) <- xs, p > 0])
  where
    total = sum (map snd xs)

-- | Equal probability for each supplied entry. Repeated values contribute
-- multiple shares; use a distinct domain when that is not intended.
uniform :: NonEmpty a -> Distribution a
uniform xs = fromBranches [(x, 1 / fromIntegral (NE.length xs)) | x <- NE.toList xs]

-- | The internal positive-weight branches. Repeated values are allowed. This
-- eliminator is useful when outcomes contain functions or existential residuals.
-- Use 'probabilities' when a canonical observable distribution is wanted.
weightedValues :: Distribution a -> [(a, Rational)]
weightedValues (Certain x) = [(x, 1)]
weightedValues (Distribution xs) = xs

probabilities :: (Ord a) => Distribution a -> [(a, Rational)]
probabilities = M.toAscList . M.fromListWith (+) . weightedValues

-- | Share equal outcomes by adding their weights, preserving total mass.
collect :: (Ord a) => Distribution a -> Distribution a
collect = fromBranches . probabilities

expectation :: (a -> Rational) -> Distribution a -> Rational
expectation f (Certain x) = f x
expectation f (Distribution xs) = sum [p * f x | (x, p) <- xs]

probability :: (a -> Bool) -> Distribution a -> Rational
probability p = expectation (\x -> if p x then 1 else 0)

condition :: (a -> Bool) -> Distribution a -> Maybe (Distribution a)
condition p (Certain x) = if p x then Just (Certain x) else Nothing
condition p (Distribution xs)
  | total == 0 = Nothing
  | otherwise = Just (fromBranches [(x, w / total) | (x, w) <- kept])
  where
    kept = filter (p . fst) xs
    total = sum (map snd kept)

instance Functor Distribution where
  fmap f (Certain x) = Certain (f x)
  fmap f (Distribution xs) = Distribution [(f x, p) | (x, p) <- xs]

instance Applicative Distribution where
  pure = Certain
  Certain f <*> xs = fmap f xs
  fs <*> Certain x = fmap ($ x) fs
  fs <*> xs = ap fs xs

instance Monad Distribution where
  Certain x >>= f = f x
  Distribution xs >>= f = Distribution (concatMap branch xs)
    where
      branch (x, p) = case f x of
        Certain y -> [(y, p)]
        Distribution ys -> [(y, p * q) | (y, q) <- ys]

instance (Ord a) => Eq (Distribution a) where
  xs == ys = probabilities xs == probabilities ys

instance (Ord a) => Ord (Distribution a) where
  compare xs ys = compare (probabilities xs) (probabilities ys)

instance (Ord a, Show a) => Show (Distribution a) where
  showsPrec d xs = showParen (d > 10) (showString "Distribution " . shows (probabilities xs))
