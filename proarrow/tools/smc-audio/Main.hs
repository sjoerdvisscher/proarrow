module Main where

import Control.Arrow ((>>>))
import Data.WAVE (WAVE (..), WAVEHeader (..), doubleToSample, putWAVEFile)
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.FilePath ((</>))
import Prelude

import SmcAudio (echo, echoPicture, melody, sampleRate, samples)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [dir] -> do
      createDirectoryIfMissing True dir
      writeAudio (dir </> "dry.wav") (samples melody)
      writeAudio (dir </> "echo.wav") (samples (melody >>> echo 0.3 0.5))
      writeFile (dir </> "echo.svg") echoPicture
      putStrLn ("Wrote dry.wav, echo.wav and echo.svg to " ++ dir)
    _ -> ioError (userError "Usage: cabal run smc-audio -- OUTPUT_DIRECTORY")

writeAudio :: FilePath -> [Double] -> IO ()
writeAudio file xs = putWAVEFile file (WAVE header (map (\x -> [doubleToSample (max (-1) (min 1 x))]) xs))
  where
    header = WAVEHeader{waveNumChannels = 1, waveFrameRate = sampleRate, waveBitsPerSample = 16, waveFrames = Nothing}
