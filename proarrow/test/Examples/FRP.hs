module Examples.FRP (test) where

import Control.Arrow qualified as A
import FRP.Yampa qualified as Y
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Prelude

import Proarrow.Profunctor.Instance.Arrow (Arr (..))
import Proarrow.Testing (expect, genNamed)
import Props.Mat ()
import SmcAudio (echo, echoWith)

test :: TestTree
test =
  testGroup
    "FRP audio (Yampa)"
    [ testProperty "an impulse produces regularly spaced, decaying echoes" $
        expect
          "echo samples"
          [1, 0, 0.5, 0, 0.25, 0, 0.125, 0]
          (Y.embed (echo 0.25 0.5) (Y.deltaEncode 0.125 [1, 0, 0, 0, 0, 0, 0, 0]))
    , testProperty "one-sample feedback follows the echo recurrence" $ do
        n <- genNamed @Int "input"
        let xs :: [Double]
            xs = map fromIntegral [n `mod` 11, 0, 3, -2, 0, 0]
            sf = unArr (echoWith (Arr (A.arr (\(dry, wet) -> dry + 0.5 * wet))) (Arr (Y.iPre 0)))
            expected = drop 1 (scanl (\previous input -> input + 0.5 * previous) 0 xs)
        expect "feedback samples" expected (Y.embed sf (Y.deltaEncode 1 xs))
    ]
