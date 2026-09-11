-- | Command-line interface for the λProlog interpreter.
module LambdaProlog.Cli (main) where

import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
  ( Parser
  , auto
  , execParser
  , fullDesc
  , header
  , help
  , helper
  , info
  , long
  , metavar
  , option
  , optional
  , progDesc
  , short
  , strArgument
  , strOption
  , switch
  , value
  )
import Options.Applicative qualified as OA
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)

import LambdaProlog.Driver
  ( Loaded (..)
  , QueryResult (..)
  , loadFile
  , loadFileQuiet
  , loadSource
  , runQueryN
  )
import LambdaProlog.Error (Error, renderError)
import LambdaProlog.Game (playGame)
import LambdaProlog.Repl (printSolutions, repl)

data Options = Options
  { optQuery :: Maybe String
  , optBatch :: Bool
  , optMax :: Int
  , optExpect :: Maybe Int
  , optPaths :: [FilePath]
  , optParseOnly :: Bool
  , optElabOnly :: Bool
  , optGame :: Bool
  , optSeed :: Maybe Integer
  , optFiles :: [FilePath]
  }

optionsP :: Parser Options
optionsP =
  Options
    <$> optional
      ( strOption
          ( long "query"
              <> short 'e'
              <> metavar "GOAL"
              <> help "Run a query and exit"
          )
      )
    <*> switch (long "batch" <> short 'b' <> help "Do not start a REPL")
    <*> option
      auto
      ( long "max"
          <> metavar "N"
          <> value maxBound
          <> help "Maximum number of solutions"
      )
    <*> optional
      ( option
          auto
          ( long "expect"
              <> metavar "N"
              <> help "Fail unless at least N solutions are found"
          )
      )
    <*> manyPath
    <*> switch (long "parse-only" <> help "Parse files and exit")
    <*> switch (long "elab-only" <> help "Elaborate files and exit")
    <*> switch (long "game" <> short 'g' <> help "Start in interactive game mode")
    <*> optional
      ( option
          auto
          ( long "seed"
              <> metavar "INT"
              <> help "Initial PRNG seed for game mode"
          )
      )
    <*> OA.many
      ( strArgument (metavar "FILE" <> help "λProlog module (.mod)")
      )
  where
    manyPath =
      OA.many
        ( strOption
            ( long "path"
                <> short 'I'
                <> metavar "DIR"
                <> help "Add a module search path"
            )
        )

main :: IO ()
main = do
  opts <- execParser $
    info
      (helper <*> optionsP)
      ( fullDesc
          <> progDesc "λProlog interpreter (higher-order hereditary Harrop)"
          <> header "lambda-prolog"
      )
  run opts

run :: Options -> IO ()
run opts = do
  let paths = optPaths opts ++ ["."]
  loaded <- loadAll opts paths (optFiles opts)
  case loaded of
    Left e -> TIO.hPutStrLn stderr (renderError e) >> exitFailure
    Right ld ->
      case optQuery opts of
        Just q -> runOne opts ld (T.pack q)
        Nothing
          | optBatch opts -> exitSuccess
          | optParseOnly opts || optElabOnly opts -> exitSuccess
          | optGame opts -> playGame paths ld (optSeed opts)
          | otherwise -> repl paths ld

loadAll :: Options -> [FilePath] -> [FilePath] -> IO (Either Error Loaded)
loadAll _opts _paths [] =
  -- Empty program (prelude only).
  pure $
    loadSource "<empty>" "module empty.\n"
loadAll opts paths (f : _)
  | optGame opts = loadFileQuiet paths f
  | otherwise = loadFile paths f

runOne :: Options -> Loaded -> T.Text -> IO ()
runOne opts ld q =
  case runQueryN ld (optMax opts) q of
    Left e -> TIO.hPutStrLn stderr (renderError e) >> exitFailure
    Right (QueryResult vars sols) -> do
      printSolutions (loadedSig ld) vars sols
      case optExpect opts of
        Just n | length sols < n -> do
          hPutStrLn stderr $
            "expected at least " ++ show n ++ " solutions, got " ++ show (length sols)
          exitFailure
        _ -> exitSuccess
