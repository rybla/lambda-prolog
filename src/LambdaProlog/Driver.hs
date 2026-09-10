-- | High-level load and query API used by the CLI and the test suite.
module LambdaProlog.Driver
  ( Loaded (..)
  , QueryResult (..)
  , ModuleQueryResult (..)
  , loadFile
  , loadFileQuiet
  , loadSource
  , runQueryText
  , runQueryN
  , interpretModuleQueries
  ) where

import Data.IntMap.Strict qualified as IntMap
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO

import LambdaProlog.Error (Error, mkErrorAt)
import LambdaProlog.Kernel.Goal (Program)
import LambdaProlog.Kernel.Pretty (PrintEnv (..), mkPrintEnv, renderTerm)
import LambdaProlog.Kernel.Search (Solution (..), queryNWithInterner)
import LambdaProlog.Kernel.Term (MetaId (..), meta)
import LambdaProlog.Surface.Elab (Sig (..), elabModule, elabQuery, elabQueryWithFrees, renderSTerm)
import LambdaProlog.Surface.Module (LoadConfig (..), loadPath)
import LambdaProlog.Surface.Parser (parseModule, parseQuery)
import LambdaProlog.Surface.Syntax (Decl (..), Module (..), QueryOption (..), STerm, termSpan)

data ModuleQueryResult = ModuleQueryResult
  { mqrOptions :: [QueryOption]
  , mqrTerm :: STerm
  , mqrVars :: [(Text, MetaId)]
  , mqrSolutions :: [Solution]
  , mqrOutput :: Text
  }
  deriving (Eq, Show)

data Loaded = Loaded
  { loadedSig :: Sig
  , loadedProg :: Program
  , loadedQueries :: [ModuleQueryResult]
  }

data QueryResult = QueryResult
  { qrVars :: [MetaId]
  , qrSolutions :: [Solution]
  }

loadFileQuiet :: [FilePath] -> FilePath -> IO (Either Error Loaded)
loadFileQuiet paths fp = do
  r <- loadPath (LoadConfig paths) fp
  case r of
    Left e -> pure (Left e)
    Right (s, p, decls) ->
      case interpretModuleQueries s p decls of
        Left e -> pure (Left e)
        Right qrs -> pure (Right (Loaded s p qrs))

loadFile :: [FilePath] -> FilePath -> IO (Either Error Loaded)
loadFile paths fp = do
  r <- loadFileQuiet paths fp
  case r of
    Left e -> pure (Left e)
    Right ld -> do
      mapM_ (TIO.putStrLn . mqrOutput) (loadedQueries ld)
      pure (Right ld)

-- | Parse and elaborate a module from source (no accumulate), running any query commands.
loadSource :: FilePath -> Text -> Either Error Loaded
loadSource name src = do
  m <- parseModule name src
  (s, p) <- elabModule m
  qrs <- interpretModuleQueries s p (modDecls m)
  pure (Loaded s p qrs)

runQueryText :: Loaded -> Text -> Either Error [Solution]
runQueryText ld qsrc = fmap qrSolutions (runQueryN ld maxBound qsrc)

runQueryN :: Loaded -> Int -> Text -> Either Error QueryResult
runQueryN ld maxN qsrc = do
  let sg = loadedSig ld
      prog = loadedProg ld
  t <- parseQuery "<query>" qsrc
  (qvars, g) <- elabQuery sg t
  Right (QueryResult qvars (queryNWithInterner maxN (sigInterner sg) prog qvars g))

-- | Interpret all query declarations in a module with their options.
interpretModuleQueries :: Sig -> Program -> [Decl] -> Either Error [ModuleQueryResult]
interpretModuleQueries sg prog decls = mapM evalOne [ (opts, t) | DQuery opts t <- decls ]
  where
    evalOne (opts, t) = do
      let hasSucceeds = QOSucceeds `elem` opts
          hasFails = QOFails `elem` opts
          mSample = listToMaybe [n | QOSample n <- opts]
      if hasSucceeds && hasFails
        then Left (mkErrorAt (termSpan t) "conflicting query options: cannot specify both 'succeeds' and 'fails'")
        else do
          (vars, goal) <- elabQueryWithFrees sg t
          let qmids = map snd vars
          if hasFails
            then do
              let sols = queryNWithInterner 1 (sigInterner sg) prog qmids goal
              case sols of
                (s : _) ->
                  Left $ mkErrorAt (termSpan t) $
                    "query expected to fail, but found solution:\n"
                    <> "  ?- " <> renderSTerm t <> ".\n"
                    <> renderCounterexample sg vars s
                [] -> do
                  let out = "?- " <> renderSTerm t <> ".\n  no"
                  pure (ModuleQueryResult opts t vars [] out)
            else do
              let sampleN = fromMaybe 1 mSample
              if hasSucceeds
                then do
                  let sols = queryNWithInterner (max 1 sampleN) (sigInterner sg) prog qmids goal
                  case sols of
                    [] ->
                      Left $ mkErrorAt (termSpan t) $
                        "query expected to succeed, but found no solutions:\n"
                        <> "  ?- " <> renderSTerm t <> "."
                    _ -> do
                      let kept = if sampleN <= 0 then [] else take sampleN sols
                          out = formatSolutions sg t vars kept sampleN
                      pure (ModuleQueryResult opts t vars kept out)
                else do
                  let sols = if sampleN <= 0 then [] else queryNWithInterner sampleN (sigInterner sg) prog qmids goal
                      out = formatSolutions sg t vars sols sampleN
                  pure (ModuleQueryResult opts t vars sols out)

formatSolutions :: Sig -> STerm -> [(Text, MetaId)] -> [Solution] -> Int -> Text
formatSolutions sg t vars sols sampleN =
  let header = "?- " <> renderSTerm t <> "."
      env = (mkPrintEnv (sigInterner sg))
        { peMetas = IntMap.fromList [(i, v) | (v, MetaId i) <- vars] }
   in case sols of
        [] | sampleN <= 0 -> header <> "\n  (0 solutions requested)"
        [] -> header <> "\n  no"
        _ | null vars -> header <> "\n  true"
        _ ->
          let renderSol sol =
                T.intercalate "\n"
                  [ "  " <> v <> " = " <> renderTerm env (IntMap.findWithDefault (meta (MetaId i)) i (solBinds sol))
                  | (v, MetaId i) <- vars
                  ]
              body = T.intercalate "\n;\n" (map renderSol sols)
           in header <> "\n" <> body

renderCounterexample :: Sig -> [(Text, MetaId)] -> Solution -> Text
renderCounterexample sg vars sol =
  let env = (mkPrintEnv (sigInterner sg))
        { peMetas = IntMap.fromList [(i, v) | (v, MetaId i) <- vars] }
   in if null vars
        then "  solution: true"
        else
          "  counterexample: "
            <> T.intercalate ", "
                [ v <> " = " <> renderTerm env (IntMap.findWithDefault (meta (MetaId i)) i (solBinds sol))
                | (v, MetaId i) <- vars
                ]
