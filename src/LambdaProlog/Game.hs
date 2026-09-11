-- | Interactive Game Driver for λProlog.
--
-- Preserves the logical kernel completely by treating game states as immutable
-- λ-terms and dispatching player query terms through state-transition relations
-- (@game_step@, @game_render@, @game_over@).
module LambdaProlog.Game
  ( GameSession (..)
  , GameHistory (..)
  , playGame
  , runGameTurn
  , initGameSession
  , renderState
  , checkGameOver
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
  , runInputT
  )
import System.CPUTime (getCPUTime)

import LambdaProlog.Driver (Loaded (..))
import LambdaProlog.Error (renderError)
import LambdaProlog.Kernel.Goal (Goal (..), Program)
import LambdaProlog.Kernel.Pretty (PrintEnv (..), mkPrintEnv, renderTerm)
import LambdaProlog.Kernel.Search (Solution (..), queryNWithInterner)
import LambdaProlog.Kernel.Term (Head (..), Lit (..), MetaId (..), Term (..), intLit, meta)
import LambdaProlog.Name (lookupName)
import LambdaProlog.Prelude (Builtins (..), prelude)
import LambdaProlog.Surface.Elab (Sig (..), elabQueryWithFrees, elabTermClosed)
import LambdaProlog.Surface.Parser (parseQuery)
import LambdaProlog.Surface.Syntax (STerm)

data GameHistory = GameHistory
  { ghTurn :: Int
  , ghState :: Term
  , ghCommand :: Text
  }
  deriving stock (Eq, Show)

data GameSession = GameSession
  { gsLoaded :: Loaded
  , gsCurrent :: Term
  , gsTurn :: Int
  , gsHistory :: [GameHistory]
  , gsRedo :: [GameHistory]
  , gsSeed :: Integer
  }

-- | Launch an interactive game session on a loaded module.
playGame :: [FilePath] -> Loaded -> Maybe Integer -> IO ()
playGame _paths loaded mSeed = do
  rawSeed <- maybe getCPUTime pure mSeed
  let seed = if rawSeed <= 0 then 12345 else rawSeed
  mSession <- initGameSession loaded seed
  case mSession of
    Left err -> TIO.putStrLn ("Cannot start game: " <> err)
    Right sess0 -> do
      TIO.putStrLn "============================================================"
      TIO.putStrLn "             Interactive λProlog Game Shell                "
      TIO.putStrLn "  Submit query terms followed by '.' (e.g. 'play 1 1.').    "
      TIO.putStrLn "  Commands: :undo, :redo, :restart, :history, :state, :quit "
      TIO.putStrLn "============================================================"
      runInputT defaultSettings (gameLoop sess0)

-- | Initialize game session by evaluating @game_init_seed Seed State@ or @game_init State@.
initGameSession :: Loaded -> Integer -> IO (Either Text GameSession)
initGameSession loaded seed = do
  let sg = loadedSig loaded
      prog = loadedProg loaded
      intern = sigInterner sg
  case lookupName "game_init_seed" intern of
    Just pInitSeed -> do
      let g = GAtom pInitSeed [intLit seed, meta (MetaId 0)]
          sols = queryNWithInterner 1 intern prog [MetaId 0] g
      case sols of
        (sol : _) ->
          case IntMap.lookup 0 (solBinds sol) of
            Just st ->
              pure $
                Right
                  GameSession
                    { gsLoaded = loaded
                    , gsCurrent = st
                    , gsTurn = 1
                    , gsHistory = []
                    , gsRedo = []
                    , gsSeed = seed
                    }
            Nothing -> pure (Left "game_init_seed did not bind State variable")
        [] -> pure (Left "game_init_seed failed to find an initial state")
    Nothing ->
      case lookupName "game_init" intern of
        Just pInit -> do
          let g = GAtom pInit [meta (MetaId 0)]
              sols = queryNWithInterner 1 intern prog [MetaId 0] g
          case sols of
            (sol : _) ->
              case IntMap.lookup 0 (solBinds sol) of
                Just st ->
                  pure $
                    Right
                      GameSession
                        { gsLoaded = loaded
                        , gsCurrent = st
                        , gsTurn = 1
                        , gsHistory = []
                        , gsRedo = []
                        , gsSeed = seed
                        }
                Nothing -> pure (Left "game_init did not bind State variable")
            [] -> pure (Left "game_init failed to find an initial state")
        Nothing ->
          pure (Left "module must define 'game_init State' or 'game_init_seed Seed State'")

gameLoop :: GameSession -> InputT IO ()
gameLoop session = do
  let sg = loadedSig (gsLoaded session)
      prog = loadedProg (gsLoaded session)
      curr = gsCurrent session
      intern = sigInterner sg
      printEnv = mkPrintEnv intern

  -- 1. Render current game state
  rendered <- liftIO $ renderState sg prog curr
  liftIO $ TIO.putStrLn rendered

  -- 2. Check game over condition
  mOver <- liftIO $ checkGameOver sg prog curr
  case mOver of
    Just endMsg -> do
      liftIO $ do
        TIO.putStrLn "\n************************************************************"
        TIO.putStrLn endMsg
        TIO.putStrLn "************************************************************"
      gameOverLoop session
    Nothing -> do
      -- 3. Prompt player for next query
      let prompt = "[Turn " <> show (gsTurn session) <> "] λΠ:game> "
      minput <- getInputLine prompt
      case minput of
        Nothing -> pure ()
        Just ":q" -> pure ()
        Just ":quit" -> pure ()
        Just ":undo" -> handleUndo session
        Just ":redo" -> handleRedo session
        Just ":restart" -> handleRestart session
        Just ":history" -> handleHistory session
        Just ":state" -> do
          liftIO $ TIO.putStrLn ("Current State: " <> renderTerm printEnv curr)
          gameLoop session
        Just ":help" -> do
          liftIO $ printHelp sg prog
          gameLoop session
        Just line
          | T.null (T.strip (T.pack line)) -> gameLoop session
          | otherwise -> do
              sess' <- liftIO $ runGameTurn session (T.pack line)
              gameLoop sess'

gameOverLoop :: GameSession -> InputT IO ()
gameOverLoop session = do
  minput <- getInputLine "[Game Over] [r]estart, [u]ndo, or [q]uit? "
  case minput of
    Nothing -> pure ()
    Just "q" -> pure ()
    Just ":q" -> pure ()
    Just ":quit" -> pure ()
    Just "r" -> handleRestart session
    Just ":restart" -> handleRestart session
    Just "u" -> handleUndo session
    Just ":undo" -> handleUndo session
    _ -> gameOverLoop session

handleUndo :: GameSession -> InputT IO ()
handleUndo session =
  case gsHistory session of
    [] -> do
      liftIO $ TIO.putStrLn "No moves to undo."
      gameLoop session
    (prev : rest) -> do
      liftIO $ TIO.putStrLn $ "[Undone move: " <> ghCommand prev <> "]"
      let redoEntry = GameHistory (gsTurn session) (gsCurrent session) "<undo>"
          sess' =
            session
              { gsCurrent = ghState prev
              , gsTurn = ghTurn prev
              , gsHistory = rest
              , gsRedo = redoEntry : gsRedo session
              }
      gameLoop sess'

handleRedo :: GameSession -> InputT IO ()
handleRedo session =
  case gsRedo session of
    [] -> do
      liftIO $ TIO.putStrLn "No moves to redo."
      gameLoop session
    (next : rest) -> do
      liftIO $ TIO.putStrLn "[Redone move]"
      let histEntry = GameHistory (gsTurn session) (gsCurrent session) "<redo>"
          sess' =
            session
              { gsCurrent = ghState next
              , gsTurn = ghTurn next
              , gsHistory = histEntry : gsHistory session
              , gsRedo = rest
              }
      gameLoop sess'

handleRestart :: GameSession -> InputT IO ()
handleRestart session = do
  r <- liftIO $ initGameSession (gsLoaded session) (gsSeed session)
  case r of
    Left err -> do
      liftIO $ TIO.putStrLn ("Restart failed: " <> err)
      gameLoop session
    Right sess' -> do
      liftIO $ TIO.putStrLn "[Game Restarted]"
      gameLoop sess'

handleHistory :: GameSession -> InputT IO ()
handleHistory session = do
  liftIO $ do
    TIO.putStrLn $ "Turns played: " <> T.pack (show (gsTurn session - 1))
    TIO.putStrLn "Move history:"
    mapM_
      ( \h ->
          TIO.putStrLn $
            "  Turn "
              <> T.pack (show (ghTurn h))
              <> ": "
              <> ghCommand h
      )
      (reverse (gsHistory session))
  gameLoop session

printHelp :: Sig -> Program -> IO ()
printHelp sg prog = do
  TIO.putStrLn $
    T.unlines
      [ "Built-in Shell Commands:"
      , "  <term>.          Submit an action or inspection query"
      , "  :undo            Undo the last move"
      , "  :redo            Redo the previously undone move"
      , "  :restart         Restart game from beginning"
      , "  :history         Display turn history"
      , "  :state           Display raw state term representation"
      , "  :help            Show this help"
      , "  :quit            Exit the game"
      ]
  case checkGameHelp sg prog of
    Just customHelp -> do
      TIO.putStrLn "Game-specific rules & commands:"
      TIO.putStrLn customHelp
    Nothing -> pure ()

-- | Execute a single game turn with user-submitted query text.
runGameTurn :: GameSession -> Text -> IO GameSession
runGameTurn session input = do
  let sg = loadedSig (gsLoaded session)
      prog = loadedProg (gsLoaded session)
      curr = gsCurrent session
      trimmed = T.strip input
      inputWithDot = if "." `T.isSuffixOf` trimmed then trimmed else trimmed <> "."

  case parseQuery "<game_input>" inputWithDot of
    Left err -> do
      TIO.putStrLn (renderError err)
      pure session
    Right sterm -> do
      mStepResult <- tryGameStep sg prog curr sterm
      case mStepResult of
        Just (nextState, mMsg) -> do
          case mMsg of
            Just msg | not (T.null msg) -> TIO.putStrLn msg
            _ -> pure ()
          let hist = GameHistory (gsTurn session) curr trimmed
          pure
            session
              { gsCurrent = nextState
              , gsTurn = gsTurn session + 1
              , gsHistory = hist : gsHistory session
              , gsRedo = []
              }
        Nothing -> do
          -- Step did not succeed; try evaluating as an inspection query
          mInspect <- tryInspectionQuery sg prog curr sterm
          case mInspect of
            Just () -> pure session
            Nothing -> do
              TIO.putStrLn "Invalid action or query failed."
              pure session

-- | Try dispatching an action through @game_step@.
tryGameStep :: Sig -> Program -> Term -> STerm -> IO (Maybe (Term, Maybe Text))
tryGameStep sg prog curr sterm = do
  let intern = sigInterner sg
  case lookupName "game_step" intern of
    Nothing -> pure Nothing
    Just pStep -> do
      case elabTermClosed sg sterm of
        Left _ -> pure Nothing
        Right actionTerm -> do
          -- Try arity 4: game_step Action Curr Next Msg
          let g4 = GAtom pStep [actionTerm, curr, meta (MetaId 0), meta (MetaId 1)]
              sols4 = queryNWithInterner 1 intern prog [MetaId 0, MetaId 1] g4
          case sols4 of
            (sol : _) ->
              case IntMap.lookup 0 (solBinds sol) of
                Just nextSt -> do
                  let mMsg = case IntMap.lookup 1 (solBinds sol) of
                        Just (TApp (HLit (LString s)) []) -> Just s
                        _ -> Nothing
                  pure (Just (nextSt, mMsg))
                Nothing -> pure Nothing
            [] -> do
              -- Try arity 3: game_step Action Curr Next
              let g3 = GAtom pStep [actionTerm, curr, meta (MetaId 0)]
                  sols3 = queryNWithInterner 1 intern prog [MetaId 0] g3
              case sols3 of
                (sol : _) ->
                  case IntMap.lookup 0 (solBinds sol) of
                    Just nextSt -> pure (Just (nextSt, Nothing))
                    Nothing -> pure Nothing
                [] -> pure Nothing

-- | Try evaluating an inspection query without advancing the game turn.
tryInspectionQuery :: Sig -> Program -> Term -> STerm -> IO (Maybe ())
tryInspectionQuery sg prog curr sterm = do
  let intern = sigInterner sg
  case lookupName "game_inspect" intern of
    Just pInspect ->
      case elabTermClosed sg sterm of
        Right queryTerm -> do
          let g = GAtom pInspect [queryTerm, curr]
              sols = queryNWithInterner 5 intern prog [] g
          case sols of
            (_ : _) -> do
              TIO.putStrLn "yes"
              pure (Just ())
            [] -> tryPlainQuery sg prog sterm
        Left _ -> tryPlainQuery sg prog sterm
    Nothing -> tryPlainQuery sg prog sterm

tryPlainQuery :: Sig -> Program -> STerm -> IO (Maybe ())
tryPlainQuery sg prog sterm =
  case elabQueryWithFrees sg sterm of
    Left _ -> pure Nothing
    Right (frees, goal) -> do
      let qmids = map snd frees
          sols = queryNWithInterner 5 (sigInterner sg) prog qmids goal
      case sols of
        [] -> pure Nothing
        _ -> do
          let env = (mkPrintEnv (sigInterner sg))
                { peMetas = IntMap.fromList [(i, v) | (v, MetaId i) <- frees] }
          if null frees
            then TIO.putStrLn "  true"
            else
              mapM_
                ( \sol ->
                    mapM_
                      ( \(v, MetaId i) ->
                          TIO.putStrLn $
                            "  "
                              <> v
                              <> " = "
                              <> renderTerm env (IntMap.findWithDefault (meta (MetaId i)) i (solBinds sol))
                      )
                      frees
                )
                sols
          pure (Just ())

-- | Render the game state using @game_render@ or fallback to @renderTerm@.
renderState :: Sig -> Program -> Term -> IO Text
renderState sg prog curr = do
  let intern = sigInterner sg
      printEnv = mkPrintEnv intern
  case lookupName "game_render" intern of
    Nothing -> pure (renderTerm printEnv curr)
    Just pRender -> do
      let g = GAtom pRender [curr, meta (MetaId 0)]
          sols = queryNWithInterner 1 intern prog [MetaId 0] g
      case sols of
        (sol : _) ->
          case IntMap.lookup 0 (solBinds sol) of
            Just outTerm -> pure (extractRenderOutput printEnv outTerm)
            Nothing -> pure (renderTerm printEnv curr)
        [] -> pure (renderTerm printEnv curr)

-- | Extract rendered string or join list of string lines.
extractRenderOutput :: PrintEnv -> Term -> Text
extractRenderOutput _ (TApp (HLit (LString s)) []) = s
extractRenderOutput env t =
  case termToList t of
    Just xs ->
      let renderElem (TApp (HLit (LString s)) []) = s
          renderElem tm = renderTerm env tm
       in T.intercalate "\n" (map renderElem xs)
    Nothing -> renderTerm env t

termToList :: Term -> Maybe [Term]
termToList (TApp (HConst c) [])
  | c == bNil prelude = Just []
termToList (TApp (HConst c) [x, xs])
  | c == bCons prelude = (x :) <$> termToList xs
termToList _ = Nothing

-- | Check if @game_over@ succeeds.
checkGameOver :: Sig -> Program -> Term -> IO (Maybe Text)
checkGameOver sg prog curr = do
  let intern = sigInterner sg
  case lookupName "game_over" intern of
    Nothing -> pure Nothing
    Just pOver -> do
      let g2 = GAtom pOver [curr, meta (MetaId 0)]
          sols2 = queryNWithInterner 1 intern prog [MetaId 0] g2
      case sols2 of
        (sol : _) ->
          case IntMap.lookup 0 (solBinds sol) of
            Just (TApp (HLit (LString msg)) []) -> pure (Just msg)
            Just other -> pure (Just (renderTerm (mkPrintEnv intern) other))
            Nothing -> pure (Just "Game Over!")
        [] -> do
          let g1 = GAtom pOver [curr]
              sols1 = queryNWithInterner 1 intern prog [] g1
          case sols1 of
            (_ : _) -> pure (Just "Game Over!")
            [] -> pure Nothing

-- | Check optional @game_help HelpText@.
checkGameHelp :: Sig -> Program -> Maybe Text
checkGameHelp sg prog =
  let intern = sigInterner sg
   in case lookupName "game_help" intern of
        Nothing -> Nothing
        Just pHelp ->
          let g = GAtom pHelp [meta (MetaId 0)]
              sols = queryNWithInterner 1 intern prog [MetaId 0] g
           in case sols of
                (sol : _) ->
                  case IntMap.lookup 0 (solBinds sol) of
                    Just (TApp (HLit (LString msg)) []) -> Just msg
                    Just other -> Just (renderTerm (mkPrintEnv intern) other)
                    Nothing -> Nothing
                [] -> Nothing
