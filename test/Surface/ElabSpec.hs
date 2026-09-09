-- | Elaboration and end-to-end query tests on small source strings.
module Surface.ElabSpec (tests) where

import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Driver (loadSource, runQueryText)
import LambdaProlog.Kernel.Search (Solution (..))

tests :: TestTree
tests =
  testGroup
    "surface.elab"
    [ testCase "append query" $
        case loadSource "lists.mod" listsSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "append (1 :: 2 :: nil) (3 :: nil) L" of
              Left e -> fail (show e)
              Right sols -> do
                assertEqual "one solution" 1 (length sols)
                assertBool "bound" (IntMap.member 0 (solBinds (sols !! 0)))
    , testCase "implication query" $
        case loadSource "imp.mod" "module imp.\ntype p o.\n" of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "p => p" of
              Left e -> fail (show e)
              Right sols -> assertBool "succeeds" (not (null sols))
    ]
  where
    listsSrc :: Text
    listsSrc =
      "module lists.\n\
      \type append list A -> list A -> list A -> o.\n\
      \append nil L L.\n\
      \append (X :: L) K (X :: M) :- append L K M.\n"
