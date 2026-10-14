{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

-- | A feedback echo, interpreted as a Yampa signal function or a string diagram.
module SmcAudio (echoWith, echo, melody, sampleRate, duration, samples, echoPicture) where

import Control.Arrow qualified as A
import FRP.Yampa qualified as Y
import Prelude hiding ((.))

import Proarrow.Category.Monoidal (Monoidal (..), MonoidalProfunctor, SymMonoidal, Tensor)
import Proarrow.Category.Monoidal.Strength (Costrong)
import Proarrow.Core (CAT, Promonad)
import Proarrow.Monoid (CocommutativeComonoid)
import Proarrow.Profunctor.Instance.Arrow (Arr (..))
import Proarrow.Tools.Diagrams.Svg (SVG (..), W (Wire), node, render)
import Proarrow.Tools.SMC (SYN (..), proc, returnA, (-<))
import Proarrow.Tools.SMC qualified as SMC

-- | Mix the input with a delayed copy of the output. The delay must break the instantaneous
-- feedback dependency. Copying the output sends it both to the delay and to the caller.
{-# INLINE echoWith #-}
echoWith
  :: forall {k} (a :: k) (p :: CAT k)
   . (SymMonoidal k, Promonad p, MonoidalProfunctor p, Costrong Tensor p, CocommutativeComonoid a)
  => p (a ** a) a
  -> p a a
  -> p a a
echoWith mix delay = proc @(F a) @(F a) \input -> SMC.do
  rec output <- mix -< (input, delay -< output)
  returnA -< output

-- | Echoes repeat every @seconds@, each scaled by @gain@. Use a positive delay and
-- @abs gain < 1@ for a decaying echo.
echo :: Double -> Double -> Y.SF Double Double
echo seconds gain = unArr (echoWith (Arr (A.arr (\(dry, wet) -> dry + gain * wet))) (Arr (Y.delay seconds 0)))

-- | A short arpeggio with a decaying envelope on each note, followed by silence for the echo tail.
melody :: Y.SF () Double
melody = Y.time A.>>> A.arr tone
  where
    tone t
      | t >= 2 = 0
      | otherwise =
          let note = floor (t / 0.25) :: Int
              age = t - fromIntegral note * 0.25
              frequency = [261.6256, 329.6276, 391.9954, 523.2511, 391.9954, 329.6276, 261.6256, 523.2511] !! note
              envelope = (1 - exp (-(200 * age))) * exp (-(16 * age))
          in 0.3 * envelope * sin (2 * pi * frequency * age)

sampleRate :: Int
sampleRate = 44100

duration :: Double
duration = 5

-- | Sample a closed signal function at the audio rate for the demo's duration.
samples :: Y.SF () Double -> [Double]
samples sf = take (round (duration * fromIntegral sampleRate)) (Y.embed sf ((), repeat (1 / fromIntegral sampleRate, Nothing)))

-- | The feedback network drawn with its mixer and delay as boxes.
echoPicture :: String
echoPicture = render (echoWith @(S '[Wire "audio"]) (node "mix: dry + 0.5 wet") (node "delay: 0.3 s"))
