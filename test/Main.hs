{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Test.Tasty (defaultMain, testGroup)
import Prelude

-- import Examples.SimplyTypedLambdaCalculus qualified as STLC
import Examples.UntypedLambdaCalculus qualified as ULC
import Props.Bool qualified as Bool
import Props.Cospan qualified as Cospan
import Props.Cost qualified as Cost
import Props.Dot qualified as Dot
import Props.FinHask qualified as FinHask
import Props.FinRel qualified as FinRel
import Props.FinSet qualified as FinSet
import Props.Free qualified as Free
import Props.Hask qualified as Hask
import Props.Kleisli qualified as Kleisli
import Props.Mat qualified as Mat
import Props.PointedHask qualified as PointedHask
import Props.Simplex qualified as Simplex
import Props.Span qualified as Span
import Props.ZX qualified as ZX

main :: IO ()
main =
  defaultMain $
    testGroup
      "tests"
      [ testGroup
          "Proarrow"
          [ Bool.test
          , Cospan.test
          , Cost.test
          , Dot.test
          , FinHask.test
          , FinRel.test
          , FinSet.test
          , Free.test
          , Hask.test
          , Kleisli.test
          , Mat.test
          , PointedHask.test
          , Simplex.test
          , Span.test
          , ZX.test
          ]
      , testGroup
          "Examples"
          [ ULC.test
          -- , STLC.test
          ]
      ]
