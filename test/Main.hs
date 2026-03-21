{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Test.Tasty (defaultMain, testGroup)
import Prelude

import Props.Bool qualified as Bool
import Props.Dot qualified as Dot
import Props.Free qualified as Free
import Props.Hask qualified as Hask
import Props.Kleisli qualified as Kleisli
import Props.Mat qualified as Mat
import Props.PointedHask qualified as PointedHask
import Props.Simplex qualified as Simplex
import Props.ZX qualified as ZX

main :: IO ()
main =
  defaultMain $
    testGroup
      "Proarrow"
      [ Bool.test
      , Dot.test
      , Free.test
      , Hask.test
      , Kleisli.test
      , Mat.test
      , PointedHask.test
      , Simplex.test
      , ZX.test
      ]
