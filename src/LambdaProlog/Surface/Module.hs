-- | Load λProlog source files, resolving @accumulate@ along a search path
-- by inlining declarations (the book's logical reading of modules).
module LambdaProlog.Surface.Module
  ( LoadConfig (..)
  , defaultLoadConfig
  , loadPath
  ) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesFileExist)
import System.FilePath ((<.>), (</>), takeDirectory)

import LambdaProlog.Error (Error, mkError)
import LambdaProlog.Kernel.Goal (Program)
import LambdaProlog.Surface.Elab (Sig, elabModule)
import LambdaProlog.Surface.Parser (parseModule)
import LambdaProlog.Surface.Syntax
  ( Decl
  , Ident (..)
  , Module (..)
  , Preamble (..)
  , identName
  )

data LoadConfig = LoadConfig
  { lcPaths :: [FilePath]
  }

defaultLoadConfig :: LoadConfig
defaultLoadConfig = LoadConfig ["."]

loadPath :: LoadConfig -> FilePath -> IO (Either Error (Sig, Program, [Decl]))
loadPath cfg path = do
  r <- collect cfg Set.empty path
  case r of
    Left e -> pure (Left e)
    Right ms ->
      let decls = concatMap modDecls ms
          combined =
            case ms of
              [] -> Left (mkError "no modules loaded")
              m : _ ->
                Right
                  m
                    { modDecls = decls
                    , modPreamble = Preamble [] [] [] []
                    }
       in pure $ do
            comb <- combined
            (sg, prog) <- elabModule comb
            pure (sg, prog, modDecls comb)

-- | Modules in dependency order (accumulated first).
collect :: LoadConfig -> Set FilePath -> FilePath -> IO (Either Error [Module])
collect cfg seen path = do
  exists <- doesFileExist path
  if not exists
    then pure (Left (mkError ("file not found: " <> T.pack path)))
    else
      if path `Set.member` seen
        then pure (Right [])
        else do
          src <- TIO.readFile path
          case parseModule path src of
            Left e -> pure (Left e)
            Right m -> do
              let dir = takeDirectory path
                  cfg' = cfg {lcPaths = dir : lcPaths cfg}
                  deps = map identName (preAccumulate (modPreamble m))
              rest <- collectDeps cfg' (Set.insert path seen) deps
              case rest of
                Left e -> pure (Left e)
                Right ms -> pure (Right (ms ++ [m]))

collectDeps ::
  LoadConfig ->
  Set FilePath ->
  [Text] ->
  IO (Either Error [Module])
collectDeps _ _ [] = pure (Right [])
collectDeps cfg seen (d : ds) = do
  resolved <- resolve cfg d
  case resolved of
    Nothing -> pure (Left (mkError ("cannot find module " <> d)))
    Just fp -> do
      a <- collect cfg seen fp
      case a of
        Left e -> pure (Left e)
        Right ms -> do
          b <- collectDeps cfg (Set.union seen (Set.fromList (map (const fp) ms))) ds
          case b of
            Left e -> pure (Left e)
            Right ns -> pure (Right (ms ++ ns))

resolve :: LoadConfig -> Text -> IO (Maybe FilePath)
resolve cfg name = go (lcPaths cfg)
  where
    base = T.unpack name
    go [] = pure Nothing
    go (p : ps) = do
      let cand = p </> base <.> "mod"
      ok <- doesFileExist cand
      if ok then pure (Just cand) else go ps
