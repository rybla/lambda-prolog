-- | High-level load and query API used by the CLI and the test suite.
module LambdaProlog.Driver
  ( Loaded (..)
  , QueryResult (..)
  , loadFile
  , loadSource
  , runQueryText
  , runQueryN
  ) where

import Data.Text (Text)

import LambdaProlog.Error (Error)
import LambdaProlog.Kernel.Goal (Program)
import LambdaProlog.Kernel.Search (Solution, queryNWithInterner)
import LambdaProlog.Kernel.Term (MetaId)
import LambdaProlog.Surface.Elab (Sig (..), elabModule, elabQuery)
import LambdaProlog.Surface.Module (LoadConfig (..), loadPath)
import LambdaProlog.Surface.Parser (parseModule, parseQuery)

data Loaded = Loaded
  { loadedSig :: Sig
  , loadedProg :: Program
  }

data QueryResult = QueryResult
  { qrVars :: [MetaId]
  , qrSolutions :: [Solution]
  }

loadFile :: [FilePath] -> FilePath -> IO (Either Error Loaded)
loadFile paths fp = do
  r <- loadPath (LoadConfig paths) fp
  pure $ fmap (\(s, p) -> Loaded s p) r

-- | Parse and elaborate a module from source (no accumulate).
loadSource :: FilePath -> Text -> Either Error Loaded
loadSource name src = do
  m <- parseModule name src
  (s, p) <- elabModule m
  pure (Loaded s p)

runQueryText :: Loaded -> Text -> Either Error [Solution]
runQueryText ld qsrc = fmap qrSolutions (runQueryN ld maxBound qsrc)

runQueryN :: Loaded -> Int -> Text -> Either Error QueryResult
runQueryN (Loaded sg prog) maxN qsrc = do
  t <- parseQuery "<query>" qsrc
  (qvars, g) <- elabQuery sg t
  Right (QueryResult qvars (queryNWithInterner maxN (sigInterner sg) prog qvars g))
