{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Test.Tasty (defaultMain, testGroup)
import Prelude

import Props.Bool qualified as Bool
import Props.Hask qualified as Hask
import Props.Kleisli qualified as Kleisli
import Props.Mat qualified as Mat
import Props.PointedHask qualified as PointedHask

main :: IO ()
main =
  defaultMain $
    testGroup
      "Proarrow"
      [ Bool.test
      , Hask.test
      , Kleisli.test
      , Mat.test
      , PointedHask.test
      ]
