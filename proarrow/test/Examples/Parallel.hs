{-# LANGUAGE QualifiedDo #-}

-- | A small build system: one SMC program supplies execution, diagrams and parallel scheduling.
module Examples.Parallel (test, demo, runSequential, runParallel, Run (..), Event (..), sequentialPicture, parallelPicture, timeline) where

import Control.Concurrent.Async qualified as Async
import Control.Concurrent.MVar (modifyMVar_, newMVar, readMVar)
import Control.Monad ((>=>))
import Data.Kind (Type)
import Data.List (isInfixOf, sort, sortOn)
import GHC.Clock (getMonotonicTimeNSec)
import System.Directory (createDirectory, createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.IO (readFile')
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Falsify (testFailed)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Falsify (testProperty)
import Text.Printf (printf)
import Prelude hiding (id, (**), (.))
import Prelude qualified as P

import Proarrow.Category.Instance.Kleisli (KLEISLI (..), Kleisli (..))
import Proarrow.Category.Instance.OpenHypergraph qualified as HG
import Proarrow.Category.Monoidal (Monoidal, MonoidalProfunctor, type (**))
import Proarrow.Category.Monoidal.Hypergraph (Sized (..))
import Proarrow.Category.Monoidal.Strictified (Strictified (..))
import Proarrow.Core (CategoryOf (..), Profunctor, Promonad (..))
import Proarrow.Functor (Prelude (..))
import Proarrow.Object (pattern Objs)
import Proarrow.Profunctor.Instance.Star (Star, pattern Star)
import Proarrow.Testing (expect)
import Proarrow.Tools.Diagrams.Svg (SVG (..), Svg (..), W (Wire), node, render)
import Proarrow.Tools.Diagrams.Svg qualified as Svg
import Proarrow.Tools.SMC (toSMC1, (-<))
import Proarrow.Tools.SMC qualified as SMC

-- In GHCi (requires ghc, haddock and tar on PATH):
--
-- cabal repl test
-- import Examples.Parallel
-- demo "/tmp/smc-build"
--
-- Jobs use isolated build directories and communicate through wires. Concurrent tensor with
-- sequential composition is not a lawful SMC for arbitrary IO with hidden shared-state effects.

-- * One pipeline, interpreted as functions, diagrams and concurrent jobs

buildGraph
  :: forall {k} (workspace :: k) sources object app executable documentation package
   . (Monoidal k)
  => (workspace ~> sources)
  -> (sources ~> object)
  -> (sources ~> object)
  -> (object ** object ~> app)
  -> (app ~> executable)
  -> (sources ~> documentation)
  -> (executable ** documentation ~> package)
  -> (HG.Wires '[workspace] :: HG.SIMPLIFY k) ~> HG.Wires '[package]
buildGraph prepare@Objs model@Objs view@Objs main@Objs link@Objs document@Objs package@Objs =
  toSMC1 \workspace -> SMC.do
    sources <- HG.prim1 prepare -< workspace
    modelObject <- HG.prim1 model -< sources
    viewObject <- HG.prim1 view -< sources
    app <- HG.prim2 main -< (modelObject, viewObject)
    executable <- HG.prim1 link -< app
    docs <- HG.prim1 document -< sources
    HG.prim2 package -< (executable, docs)

newtype Workspace = Workspace FilePath
newtype Sources = Sources FilePath
newtype Object = Object FilePath

-- An application contains Main.o together with its dependencies.
data App = App FilePath [FilePath]
newtype Executable = Executable FilePath
newtype Documentation = Documentation FilePath
newtype Package = Package FilePath

sourceFiles :: [(String, String)]
sourceFiles =
  [
    ( "Model"
    , unlines
        [ "-- | Sample data for the chart application."
        , "module Model where"
        , "-- | The values to plot."
        , "values :: [Int]"
        , "values = [4, 7, 2, 9]"
        ]
    )
  ,
    ( "View"
    , unlines
        [ "-- | Rendering the chart."
        , "module View where"
        , "-- | Draw one bar per value."
        , "chart :: [Int] -> String"
        , "chart ns = unlines [replicate n '#' | n <- ns]"
        ]
    )
  ,
    ( "Main"
    , unlines
        [ "-- | The chart application."
        , "module Main where"
        , "import Model"
        , "import View"
        , "main :: IO ()"
        , "main = putStr (chart values)"
        ]
    )
  ]

expected :: String
expected = "####\n#######\n##\n#########\n"

command :: FilePath -> [String] -> IO String
command program args = do
  (status, out, err) <- readProcessWithExitCode program args ""
  case status of
    ExitSuccess -> pure out
    ExitFailure code -> fail (unwords (program : args) ++ " failed (" ++ show code ++ ")\n" ++ out ++ err)

prepareSources :: Workspace -> IO Sources
prepareSources (Workspace root) = do
  createDirectory (root </> "src")
  mapM_ (\(name, text) -> writeFile (root </> "src" </> name ++ ".hs") text) sourceFiles
  pure (Sources root)

compileModule :: String -> Sources -> IO Object
compileModule name (Sources root) = do
  let output = root </> name
  createDirectory output
  _ <- command "ghc" ["-v0", "-O0", "-c", root </> "src" </> name ++ ".hs", "-odir", output, "-hidir", output]
  pure (Object (output </> name ++ ".o"))

compileMain :: (Object, Object) -> IO App
compileMain (Object model, Object view) = do
  let root = takeDirectory (takeDirectory model)
      output = root </> "Main"
  createDirectory output
  _ <-
    command
      "ghc"
      [ "-v0"
      , "-O0"
      , "-c"
      , root </> "src" </> "Main.hs"
      , "-i" ++ takeDirectory model
      , "-i" ++ takeDirectory view
      , "-odir"
      , output
      , "-ohi"
      , output </> "Main.hi"
      ]
  pure (App root [model, view, output </> "Main.o"])

linkApp :: App -> IO Executable
linkApp (App root objects) = do
  let path = root </> "app"
  _ <- command "ghc" (["-v0", "-o", path] ++ objects)
  pure (Executable path)

generateDocs :: Sources -> IO Documentation
generateDocs (Sources root) = do
  let output = root </> "docs"
  _ <-
    command
      "haddock"
      ( ["--html", "--hyperlinked-source", "--title=Chart demo", "--odir=" ++ output]
          ++ [root </> "src" </> name ++ ".hs" | (name, _) <- sourceFiles]
      )
  pure (Documentation output)

packageApp :: (Executable, Documentation) -> IO Package
packageApp (Executable executable, Documentation docs) = do
  let root = takeDirectory executable
      archive = root </> "app.tar.gz"
  _ <-
    command
      "tar"
      ["-czf", archive, "-C", root, "app", "-C", takeDirectory docs, takeFileName docs]
  pure (Package archive)

-- * Execution

-- Star supplies the profunctor and concurrent tensor through Concurrently's applicative.
-- Job adds sequential composition locally for isolated jobs: independent effects must commute,
-- and scheduling differences are ignored when comparing results.
type Job :: Type -> Type -> Type
newtype Job a b = Job (Star (Prelude Async.Concurrently) a b)
  deriving newtype (Profunctor, MonoidalProfunctor)

fromIO :: (a -> IO b) -> Job a b
fromIO f = Job (Star (Prelude P.. Async.Concurrently P.. f))

runJob :: Job a b -> a -> IO b
runJob (Job (Star f)) = Async.runConcurrently P.. unPrelude P.. f

instance Promonad Job where
  id = fromIO pure
  g . f = fromIO (runJob f >=> runJob g)

instance Sized (KLEISLI Job) where
  sizeOf = 2

runWith :: HG.Wiring (KLEISLI Job) -> IO Run
runWith wiring = withBuildRun \workspace record -> do
  let job :: String -> (a -> IO b) -> Kleisli (KL a :: KLEISLI Job) (KL b)
      job name action = Kleisli (loggedJob record name action)
      graph =
        buildGraph
          (job "prepare sources" prepareSources)
          (job "compile Model" (compileModule "Model"))
          (job "compile View" (compileModule "View"))
          (job "compile Main" compileMain)
          (job "link" linkApp)
          (job "generate docs" generateDocs)
          (job "package" packageApp)
  Str (Kleisli execute) <- either fail pure (HG.simplify wiring graph)
  runJob execute workspace

runSequential :: IO Run
runSequential = runWith HG.copyDiscard

runParallel :: IO Run
runParallel = runWith (HG.layered HG.copyDiscard)

-- * Demo support

data Event = Event {seconds :: Double, jobName :: String, phase :: String} deriving stock (Eq, Show)
data Run = Run {result :: String, elapsed :: Double, events :: [Event]} deriving stock (Eq, Show)

loggedJob :: (String -> String -> IO ()) -> String -> (a -> IO b) -> Job a b
loggedJob record name action = fromIO \a -> do
  record name "start"
  b <- action a
  record name "finish"
  pure b

-- Measure only the build, then verify its package and remove the temporary workspace.
withBuildRun :: (Workspace -> (String -> String -> IO ()) -> IO Package) -> IO Run
withBuildRun build = withSystemTempDirectory "proarrow-build" \root -> do
  logbook <- newMVar []
  started <- getMonotonicTimeNSec
  let sinceStart = do
        now <- getMonotonicTimeNSec
        pure (fromIntegral (now - started) / 1e9)
      record name status = do
        t <- sinceStart
        modifyMVar_ logbook (pure P.. (Event t name status :))
  package <- build (Workspace root) record
  duration <- sinceStart
  trace <- sortOn seconds <$> readMVar logbook
  value <- verifyPackage package
  pure (Run value duration trace)

verifyPackage :: Package -> IO String
verifyPackage (Package archive) = do
  let unpacked = takeDirectory archive </> "unpacked"
  createDirectory unpacked
  _ <- command "tar" ["-xzf", archive, "-C", unpacked]
  value <- command (unpacked </> "app") []
  contents <- readFile' (unpacked </> "docs" </> "index.html")
  if value == expected && "Chart demo" `isInfixOf` contents
    then pure value
    else fail "packaged application or documentation is incorrect"

-- | Build and check both schedules, saving diagrams and measured timelines in the given directory.
-- The installed GHC and host load affect timings; concurrency need not make a tiny build faster.
demo :: FilePath -> IO ()
demo directory = do
  createDirectoryIfMissing True directory
  sequential <- runSequential
  parallel <- runParallel
  display "Sequential" sequential
  display "Layered" parallel
  either fail (writeFile (directory </> "sequential.svg")) sequentialPicture
  either fail (writeFile (directory </> "parallel.svg")) parallelPicture
  writeFile (directory </> "timeline.svg") (timeline sequential parallel)
  putStrLn ("Diagrams and measured timeline: " ++ directory)
  putStrLn ("Packaged executable output:\n" ++ result parallel)
  where
    display title run = do
      putStrLn title
      mapM_ (\(Event t name status) -> printf "  %5.3fs  %-14s %s\n" t name status) (events run)
      printf "  total: %.3fs\n\n" (elapsed run)

-- | Both measured schedules on the same time scale. Job names come from this example's fixed labels.
timeline :: Run -> Run -> String
timeline sequential parallel =
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
    ++ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"900\" height=\"570\" viewBox=\"0 0 900 570\">"
    ++ "<rect width=\"900\" height=\"570\" fill=\"white\"/><g font-family=\"sans-serif\" font-size=\"14\">"
    ++ panel 28 "Sequential build" sequential
    ++ panel 300 "Automatic parallel build" parallel
    ++ "</g></svg>"
  where
    scale = 640 / max 0.001 (max (elapsed sequential) (elapsed parallel))
    names = ["prepare sources", "compile Model", "compile View", "compile Main", "link", "generate docs", "package"]
    panel :: Int -> String -> Run -> String
    panel y title run =
      printf "<text x=\"20\" y=\"%d\" font-weight=\"bold\">%s: %.3fs</text>" y title (elapsed run)
        ++ concat [bar (y + 18 + i * 28) name run | (i, name) <- zip [0 ..] names]
        ++ printf "<path d=\"M180 %d H820\" stroke=\"#aaa\"/>" (y + 228)
        ++ concat
          [ printf
              "<text x=\"%.2f\" y=\"%d\" text-anchor=\"middle\" fill=\"#555\">%.2fs</text>"
              (180 + t * scale)
              (y + 248)
              t
          | i <- [0 .. 4 :: Int]
          , let t = fromIntegral i * max (elapsed sequential) (elapsed parallel) / 4
          ]
    bar :: Int -> String -> Run -> String
    bar y name run =
      printf "<text x=\"20\" y=\"%d\">%s</text>" (y + 15) name
        ++ concat
          [ printf
              "<rect x=\"%.2f\" y=\"%d\" width=\"%.2f\" height=\"21\" rx=\"3\" fill=\"#4078b5\"/>"
              (180 + start * scale)
              y
              (max 2 ((end - start) * scale))
          | Event start job "start" <- events run
          , job == name
          , Event end job' "finish" <- events run
          , job' == name
          ]

-- * Pictures and pure checks

picture :: HG.Wiring SVG -> Either String (Svg (S '[Wire "dir"]) (S '[Wire "pkg"]))
picture wiring = do
  Str diagram <-
    HG.simplify wiring $
      buildGraph
        (node @'[Wire "dir"] @'[Wire "src"] "prepare sources")
        (node @'[Wire "src"] @'[Wire "obj"] "compile Model")
        (node @'[Wire "src"] @'[Wire "obj"] "compile View")
        (node @'[Wire "obj", Wire "obj"] @'[Wire "app"] "compile Main")
        (node @'[Wire "app"] @'[Wire "exe"] "link")
        (node @'[Wire "src"] @'[Wire "doc"] "generate docs")
        (node @'[Wire "exe", Wire "doc"] @'[Wire "pkg"] "package")
  pure diagram

sequentialPicture, parallelPicture :: Either String String
sequentialPicture = render <$> picture HG.copyDiscard
parallelPicture = render <$> picture (HG.layered HG.copyDiscard)

-- Gate groups in a composition, with tensor operands sharing a stage.
stages :: Svg.Diagram -> [[String]]
stages = \case
  Svg.Node _ title _ _ -> [[title]]
  Svg.Seq a b -> stages a ++ stages b
  Svg.Beside a b -> together (stages a) (stages b)
  Svg.Trace _ d -> stages d
  _ -> []
  where
    together [] bs = bs
    together as [] = as
    together (a : as) (b : bs) = (a ++ b) : together as bs

test :: TestTree
test =
  testGroup
    "Parallel build"
    [ testProperty "sequential job dependencies" $
        case picture HG.copyDiscard of
          Left err -> testFailed err
          Right (Svg _ diagram) ->
            expect
              "stages"
              [["prepare sources"], ["compile Model"], ["compile View"], ["compile Main"], ["link"], ["generate docs"], ["package"]]
              (map sort (stages diagram))
    , testProperty "layered jobs respect dependencies" $
        case picture (HG.layered HG.copyDiscard) of
          Left err -> testFailed err
          Right (Svg _ diagram) ->
            expect
              "stages"
              [["prepare sources"], ["compile Model", "compile View", "generate docs"], ["compile Main"], ["link"], ["package"]]
              (map sort (stages diagram))
    ]
