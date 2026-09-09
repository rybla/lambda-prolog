-- | Interactive read-eval-print loop (Teyjus-style).
module LambdaProlog.Repl
  ( repl
  , printSolutions
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Console.Haskeline
  ( InputT
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )
import System.IO (hFlush, stdout)

import LambdaProlog.Driver (Loaded (..), QueryResult (..), loadFile, runQueryN)
import LambdaProlog.Error (renderError)
import LambdaProlog.Kernel.Pretty (PrintEnv, mkPrintEnv, renderTerm)
import LambdaProlog.Kernel.Search (Solution (..))
import LambdaProlog.Kernel.Term (MetaId (..), meta)
import LambdaProlog.Surface.Elab (Sig (..))

repl :: [FilePath] -> Loaded -> IO ()
repl searchPath loaded0 = runInputT defaultSettings (loop searchPath loaded0)
  where
    loop paths loaded = do
      minput <- getInputLine "λΠ> "
      case minput of
        Nothing -> pure ()
        Just ":quit" -> pure ()
        Just ":q" -> pure ()
        Just ":help" -> do
          liftIO $
            TIO.putStrLn $
              T.unlines
                [ "  <goal>.          solve a query"
                , "  :load FILE       load a module"
                , "  :reload          reload last file"
                , "  :help            this message"
                , "  :quit            exit"
                ]
          loop paths loaded
        Just (':':'l':'o':'a':'d':' ':fp) -> do
          r <- liftIO $ loadFile paths fp
          case r of
            Left e -> liftIO (TIO.putStrLn (renderError e)) >> loop paths loaded
            Right ld -> liftIO (TIO.putStrLn ("loaded " <> T.pack fp)) >> loop paths ld
        Just line
          | T.null (T.strip (T.pack line)) -> loop paths loaded
          | otherwise -> do
              liftIO $ handleQuery loaded (T.pack line)
              loop paths loaded

handleQuery :: Loaded -> Text -> IO ()
handleQuery loaded q = case runQueryN loaded maxBound q of
  Left e -> TIO.putStrLn (renderError e)
  Right (QueryResult vars sols) -> printSolutions (loadedSig loaded) vars sols

printSolutions :: Sig -> [MetaId] -> [Solution] -> IO ()
printSolutions _ _ [] = TIO.putStrLn "no"
printSolutions sg vars sols = go sols
  where
    env = mkPrintEnv (sigInterner sg)
    go [] = TIO.putStrLn "no (more) solutions"
    go (s : ss) = do
      TIO.putStrLn "The answer substitution:"
      printBinds env vars s
      if null ss
        then TIO.putStrLn "yes"
        else do
          TIO.putStr "More solutions (y/n)? "
          hFlush stdout
          ans <- getLine
          if ans `elem` ["n", "N", ""]
            then TIO.putStrLn "yes"
            else go ss

printBinds :: PrintEnv -> [MetaId] -> Solution -> IO ()
printBinds env vars sol =
  if null vars
    then TIO.putStrLn "  true"
    else
      mapM_
        ( \m@(MetaId i) ->
            let tm = IntMap.findWithDefault (meta m) i (solBinds sol)
             in TIO.putStrLn $
                  "  X" <> T.pack (show i) <> " = " <> renderTerm env tm
        )
        vars
