{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Test.Tasty (defaultMain, testGroup)
import Prelude

import Examples.Cbpv qualified as Cbpv
import Examples.CustomLaws qualified as CustomLaws
import Examples.Database qualified as Database
import Examples.Free qualified as FreeExample
import Examples.Graph qualified as Graph
import Examples.IntComposition qualified as IntComposition
import Examples.LinearLogic qualified as LinearLogic
import Examples.Sessions qualified as Sessions
import Examples.SimplyTypedLambdaCalculus qualified as STLC
import Examples.Toffoli qualified as Toffoli
import Examples.UntypedLambdaCalculus qualified as ULC
import Examples.Vitrea qualified as Vitrea
import Props.Bool qualified as Bool
import Props.Cospan qualified as Cospan
import Props.Cost qualified as Cost
import Props.Cps qualified as Cps
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
import Props.IntConstruction qualified as IntConstruction
import Props.Kleisli qualified as Kleisli
import Props.Mat qualified as Mat
import Props.OpenHypergraph qualified as OpenHypergraph
import Props.Optic.FinRel qualified as OpticFinRel
import Props.Optic.Hask qualified as Optic
import Props.Optic.Linear qualified as OpticLinear
import Props.Ordinal qualified as Ordinal
import Props.Paths qualified as Paths
import Props.PointedHask qualified as PointedHask
import Props.SMC qualified as SMC
import Props.Sheaf qualified as Sheaf
import Props.Sheaf.Chain qualified as SheafChain
import Props.Sheaf.Collage qualified as SheafCollage
import Props.Simplex qualified as Simplex
import Props.Span qualified as Span
import Props.Svg qualified as Svg
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
          , OpenHypergraph.test
          , Cost.test
          , DPO.test
          , Dot.test
          , FinHask.test
          , FinRel.test
          , IntConstruction.test
          , FinSet.test
          , Finitary.test
          , FinitaryGraph.test
          , Free.test
          , Hask.test
          , Kleisli.test
          , Cps.test
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
          , SMC.test
          , Span.test
          , Svg.test
          , ZX.test
          ]
      , testGroup
          "Examples"
          [ CustomLaws.test
          , Database.test
          , FreeExample.test
          , Graph.test
          , STLC.test
          , ULC.test
          , IntComposition.test
          , LinearLogic.test
          , Sessions.test
          , Cbpv.test
          , Toffoli.test
          , Vitrea.test
          ]
      ]
