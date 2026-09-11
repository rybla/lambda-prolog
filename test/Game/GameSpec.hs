-- | Unit and integration tests for the λProlog Game Engine.
module Game.GameSpec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Driver (loadFileQuiet)
import LambdaProlog.Game
  ( GameHistory (..)
  , GameSession (..)
  , initGameSession
  , runGameTurn
  )
import LambdaProlog.Kernel.Builtin (lcgStep, lcgVal)

tests :: TestTree
tests =
  testGroup
    "game.engine"
    [ testCase "prng lcgStep determinism" $ do
        let s1 = lcgStep 42
            s2 = lcgStep 42
        assertEqual "deterministic next seed" s1 s2
        assertBool "non-zero seed" (s1 /= 0)

    , testCase "prng lcgVal non-negative 31-bit" $ do
        let v1 = lcgVal 12345
            v2 = lcgVal (lcgStep 12345)
        assertBool "v1 >= 0" (v1 >= 0)
        assertBool "v1 < 2^31" (v1 < 2147483648)
        assertBool "v2 >= 0" (v2 >= 0)
        assertBool "v2 < 2^31" (v2 < 2147483648)
        assertBool "distinct values" (v1 /= v2)

    , testCase "tictactoe game_init and step" $ do
        r <- loadFileQuiet ["examples", "."] "examples/tictactoe.mod"
        case r of
          Left err -> assertBool ("load tictactoe failed: " ++ show err) False
          Right ld -> do
            sessRes <- initGameSession ld 42
            case sessRes of
              Left err -> assertBool ("init failed: " ++ show err) False
              Right sess0 -> do
                assertEqual "initial turn is 1" 1 (gsTurn sess0)
                assertEqual "initial history is empty" [] (gsHistory sess0)
                -- Execute player move: play 2 2.
                sess1 <- runGameTurn sess0 "play 2 2."
                assertEqual "turn advances to 2" 2 (gsTurn sess1)
                assertEqual "history has 1 item" 1 (length (gsHistory sess1))
                assertEqual "history recorded command" "play 2 2." (ghCommand (head (gsHistory sess1)))

    , testCase "dungeon adventure navigation, inventory, and undo" $ do
        r <- loadFileQuiet ["examples", "."] "examples/dungeon.mod"
        case r of
          Left err -> assertBool ("load dungeon failed: " ++ show err) False
          Right ld -> do
            sessRes <- initGameSession ld 777
            case sessRes of
              Left err -> assertBool ("init failed: " ++ show err) False
              Right sess0 -> do
                assertEqual "initial turn is 1" 1 (gsTurn sess0)
                -- Step 1: go north to hall
                sess1 <- runGameTurn sess0 "go \"north\"."
                assertEqual "turn is 2" 2 (gsTurn sess1)
                -- Step 2: go east to library
                sess2 <- runGameTurn sess1 "go \"east\"."
                assertEqual "turn is 3" 3 (gsTurn sess2)
                -- Step 3: take bronze_key
                sess3 <- runGameTurn sess2 "take \"bronze_key\"."
                assertEqual "turn is 4" 4 (gsTurn sess3)
                -- Step 4: inspection query (should NOT advance turn)
                sess4 <- runGameTurn sess3 "room_exits \"hall\" Ex."
                assertEqual "inspection does not advance turn" 4 (gsTurn sess4)
    ]
