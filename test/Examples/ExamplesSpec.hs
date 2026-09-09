-- | End-to-end tests of the example programs.
module Examples.ExamplesSpec (tests) where

import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

import LambdaProlog.Driver (loadFile, runQueryText)

tests :: TestTree
tests =
  testGroup
    "examples"
    [ ex "lists.mod" "append (1 :: 2 :: nil) (3 :: nil) L"
    , ex "tutorial.mod" "append (1 :: nil) (2 :: nil) L"
    , ex "hypothetical.mod" "edge b c => path a c"
    , ex "hidden_reverse.mod" "reverse (1 :: 2 :: 3 :: nil) K"
    , ex "typeinf.mod" "of (abs (y\\ y)) (arrow A A)"
    , ex "hoas_lambda.mod" "eval (abs (x\\ x)) V"
    , ex "prenex.mod" "prenex (all (x\\ atom x)) D"
    , ex "tacticals.mod" "idtac p p"
    ]
  where
    ex file q =
      testCase file $ do
        r <- loadFile ["examples", "."] ("examples/" ++ file)
        case r of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld (T.pack q) of
              Left e -> fail (show e)
              Right sols -> assertBool "has a solution" (not (null sols))
