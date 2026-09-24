{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Test.Tasty (defaultMain, testGroup)
import Prelude

import Examples.Database qualified as Database
import Examples.Free qualified as FreeExample
import Examples.Graph qualified as Graph
import Examples.SimplyTypedLambdaCalculus qualified as STLC
import Examples.UntypedLambdaCalculus qualified as ULC
import Examples.Vitrea qualified as Vitrea
import Props.Bool qualified as Bool
import Props.Cospan qualified as Cospan
import Props.Cost qualified as Cost
import Props.DPO qualified as DPO
import Props.Discrete qualified as Discrete
import Props.Dot qualified as Dot
import Props.FinHask qualified as FinHask
import Props.FinRel qualified as FinRel
import Props.FinSet qualified as FinSet
import Props.Finitary qualified as Finitary
import Props.Finitary.Graph qualified as FinitaryGraph
import Props.Free qualified as Free
import Props.Hask qualified as Hask
import Props.Kleisli qualified as Kleisli
import Props.Mat qualified as Mat
import Props.Optic.FinRel qualified as OpticFinRel
import Props.Optic.Hask qualified as Optic
import Props.Optic.Linear qualified as OpticLinear
import Props.Ordinal qualified as Ordinal
import Props.Paths qualified as Paths
import Props.PointedHask qualified as PointedHask
import Props.Sheaf qualified as Sheaf
import Props.Sheaf.Chain qualified as SheafChain
import Props.Sheaf.Collage qualified as SheafCollage
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
          , Discrete.test
          , Cospan.test
          , Cost.test
          , DPO.test
          , Dot.test
          , FinHask.test
          , FinRel.test
          , FinSet.test
          , Finitary.test
          , FinitaryGraph.test
          , Free.test
          , Hask.test
          , Kleisli.test
          , Mat.test
          , Optic.test
          , OpticLinear.test
          , OpticFinRel.test
          , Ordinal.test
          , Paths.test
          , PointedHask.test
          , Sheaf.test
          , SheafChain.test
          , SheafCollage.test
          , Simplex.test
          , Span.test
          , ZX.test
          ]
      , testGroup
          "Examples"
          [ Database.test
          , FreeExample.test
          , Graph.test
          , STLC.test
          , ULC.test
          , Vitrea.test
          ]
      ]
