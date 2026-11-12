{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- Keep the explicit mapping and binding expressions under test.
{- HLINT ignore "Use void" -}
{- HLINT ignore "Monad law, left identity" -}
{- HLINT ignore "Monad law, right identity" -}
{- HLINT ignore "Use >=>" -}

module Props.Probability (test) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Examples.OpenGames.Probability
import Proarrow.Testing (check, expect, genNamed)
import Props.Hask ()
import Props.OpenGame (Table (..))

test :: TestTree
test =
  testGroup
    "Probability"
    [ testProperty "weighted construction validates and normalises" $ do
        expect "negative probability" (Left NegativeWeight) (weighted [(True, -1), (False, 2)])
        expect "zero mass" (Left ZeroMass) (weighted [(True, 0)])
        expect "empty distribution" (Left ZeroMass) (weighted ([] :: [(Bool, Rational)]))
        expect
          "normalisation and zero removal"
          (Right [(True, 1)])
          (probabilities <$> weighted [(True, 5), (False, 0)])
    , testProperty "canonical probability combines repeated branches" $ do
        let d = weighted [(False, 1), (False, 1), (True, 2)]
        expect "branch splitting" (Right (uniform [False, True])) d
        expect "mapping combines outcomes" [((), 1)] (probabilities (() <$ uniform [False, True]))
    , testProperty "conditioning rejects impossible events and computes exact posteriors" $ do
        let d = either (error . show) id (weighted [(False, 1), (True, 3)])
        expect "impossible event" Nothing (condition (const False) d)
        expect "posterior" (Just (pure True)) (condition id d)
        expect "expected value" (3 / 4) (expectation (\x -> if x then 1 else 0) d)
    , testProperty "distribution monad left identity" $ do
        x <- genNamed @Bool "x"
        Table f <- genNamed @(Table Bool (Distribution Bool)) "f"
        expect "left identity" (f x) (pure x >>= f)
    , testProperty "distribution monad right identity" $ do
        d <- genNamed @(Distribution Bool) "d"
        expect "right identity" d (d >>= pure)
    , testProperty "distribution monad associativity" $ do
        d <- genNamed @(Distribution Bool) "d"
        Table f <- genNamed @(Table Bool (Distribution Bool)) "f"
        Table g <- genNamed @(Table Bool (Distribution Bool)) "g"
        expect "associativity" ((d >>= f) >>= g) (d >>= (\x -> f x >>= g))
    , testProperty "draws are independent unless their sampled value is shared" $ do
        let coin = uniform [False, True]
            independent = do a <- coin; b <- coin; pure (a == b)
            shared = do a <- coin; pure (a == a)
        expect "independent draws" (1 / 2) (probability id independent)
        expect "shared sample" 1 (probability id shared)
        check "normalisation" (sum (map snd (weightedValues independent)) == 1)
    , testProperty "deterministic paths keep unused payloads lazy" $ do
        let unused :: Distribution Bool
            unused = pure (error "unused deterministic payload was forced")
        expect "mapping a constant" 7 (expectation id (7 <$ unused))
        expect "binding a constant" 7 (expectation id (unused >> pure 7))
    ]
