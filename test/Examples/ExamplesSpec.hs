-- | End-to-end tests of the example programs. Each query is a regression
-- case: if the interpreter disagrees, the test names the file and goal.
module Examples.ExamplesSpec (tests) where

import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Driver (loadFile, runQueryText)
import LambdaProlog.Error (renderError)

tests :: TestTree
tests =
  testGroup
    "examples"
    [ succeeds "lists.mod" "append (1 :: 2 :: nil) (3 :: nil) L"
    , succeeds "lists.mod" "reverse (1 :: 2 :: 3 :: nil) K"
    , succeeds "lists.mod" "length (1 :: 2 :: 3 :: nil) N"
    , succeeds "lists.mod" "nth 1 (10 :: 20 :: 30 :: nil) X"
    , succeeds "lists.mod" "member 2 (1 :: 2 :: 2 :: nil)"
    , nsols "lists.mod" "memb 2 (1 :: 2 :: 2 :: nil)" 2
    , succeeds "lists.mod" "zip (1 :: nil) (2 :: nil) (pr 1 2 :: nil)"
    , succeeds "lists.mod" "assoc 1 2 (pr 1 2 :: pr 3 4 :: nil)"
    , succeeds "lists.mod" "flatten ((1 :: nil) :: (2 :: 3 :: nil) :: nil) L"
    , succeeds "lists.mod" "join (1 :: 2 :: nil) (2 :: 3 :: nil) L"
    , succeeds "tutorial.mod" "append (1 :: nil) (2 :: nil) L"
    , succeeds "tutorial.mod" "edge a b => edge b c => path a c"
    , succeeds "tutorial.mod" "pi x\\ ident x x"
    , succeeds "tutorial.mod" "copy (abs (x\\ x)) M"
    , succeeds "hypothetical.mod" "edge b c => path a c"
    , fails "hypothetical.mod" "path a c"
    , succeeds "hidden_reverse.mod" "reverse (1 :: 2 :: 3 :: nil) K"
    , succeeds "typeinf.mod" "of (abs (y\\ y)) (arrow A A)"
    , succeeds "typeinf.mod" "hastype (abs (y\\ y))"
    , succeeds "hoas_lambda.mod" "eval (abs (x\\ x)) V"
    , succeeds "hoas_lambda.mod" "eval (app (abs (x\\ x)) (abs (y\\ y))) V"
    , succeeds "hoas_lambda.mod" "copy (abs (x\\ x)) M"
    , succeeds "hoas_lambda.mod" "size (abs (x\\ x)) N"
    , succeeds "prenex.mod" "prenex (all (x\\ atom x)) D"
    , succeeds "prenex.mod" "prenex (and (all (x\\ atom x)) (atom a)) D"
    , succeeds "tacticals.mod" "idtac p p"
    , succeeds "tacticals.mod" "ptac p (andgoal q r)"
    , succeeds "tacticals.mod" "then ptac (orelse qtac rtac) p (andgoal truegoal truegoal)"
    , succeeds "maps.mod" "append (1 :: nil) (2 :: nil) L"
    , succeeds "maps.mod" "mappred age (\"bob\" :: \"sue\" :: nil) L"
    , succeeds "maps.mod" "mapfun (x\\ x) (1 :: 2 :: nil) L"
    , succeeds "control.mod" "once true"
    , succeeds "control.mod" "ifte fail fail true"
    , succeeds "nat.mod" "min 3 1 M"
    , succeeds "nat.mod" "even 4"
    , fails "nat.mod" "odd 4"
    , succeeds "nat.mod" "between 1 3 N"
    , succeeds "nat.mod" "abs (~ 4) A"
    , succeeds "sets.mod" "subset (1 :: nil) (1 :: 2 :: nil)"
    , succeeds "sets.mod" "union (1 :: nil) (1 :: 2 :: nil) U"
    , succeeds "assoc.mod" "addassoc 1 2 nil L"
    , succeeds "lists.mod" "same_length (1 :: nil) (2 :: nil)"
    , succeeds "lists.mod" "nextto 1 2 (1 :: 2 :: 3 :: nil)"
    , succeeds "lists.mod" "snoc 3 (1 :: 2 :: nil) L"
    , succeeds "lists.mod" "init (1 :: 2 :: 3 :: nil) L"
    , succeeds "lists.mod" "delete_all 1 (1 :: 2 :: 1 :: nil) L"
    , succeeds "lists.mod" "nub (1 :: 1 :: 2 :: nil) L"
    , succeeds "lists.mod" "permute (1 :: 2 :: nil) (2 :: 1 :: nil)"
    , nsols "lists.mod" "permute (1 :: 2 :: nil) K" 2
    , succeeds "lists.mod" "count 1 (1 :: 2 :: 1 :: nil) N"
    , succeeds "lists.mod" "replicate 3 7 L"
    , succeeds "lists.mod" "sum_list (1 :: 2 :: 3 :: nil) N"
    , succeeds "lists.mod" "max_list (1 :: 3 :: 2 :: nil) N"
    , succeeds "lists.mod" "min_list (1 :: 3 :: 2 :: nil) N"
    , succeeds "lists.mod" "take 2 (1 :: 2 :: 3 :: nil) L"
    , succeeds "lists.mod" "drop 2 (1 :: 2 :: 3 :: nil) L"
    , succeeds "lists.mod" "last (1 :: 2 :: 3 :: nil) X"
    , succeeds "lists.mod" "is_prefix (1 :: nil) (1 :: 2 :: nil)"
    , succeeds "lists.mod" "suffix (2 :: nil) (1 :: 2 :: nil)"
    , succeeds "maps.mod" "filter (x\\ x > 1) (1 :: 2 :: 3 :: nil) L"
    , succeeds "maps.mod" "for_each (x\\ x > 0) (1 :: 2 :: nil)"
    , succeeds "maps.mod" "partition (x\\ x > 1) (1 :: 2 :: 3 :: nil) A B"
    , succeeds "maps.mod" "exists_pred (x\\ x = 2) (1 :: 2 :: 3 :: nil)"
    , fails "maps.mod" "exists_pred (x\\ x = 9) (1 :: 2 :: 3 :: nil)"
    , succeeds "maps.mod" "find (x\\ x > 1) (1 :: 2 :: 3 :: nil) X"
    , succeeds "maps.mod" "map2 (x\\ y\\ z\\ z is x + y) (1 :: 2 :: nil) (10 :: 20 :: nil) L"
    , succeeds "control.mod" "call (true, true)"
    , succeeds "control.mod" "once (true, true)"
    , fails "control.mod" "once (fail, true)"
    , succeeds "control.mod" "ifte true true fail"
    , succeeds "control.mod" "ignore fail"
    , succeeds "nat.mod" "gcd 12 8 D"
    , succeeds "nat.mod" "pow 2 3 N"
    , succeeds "nat.mod" "succ 3 N"
    , succeeds "nat.mod" "sign (~ 4) S"
    , succeeds "nat.mod" "max 3 1 M"
    , succeeds "sets.mod" "difference (1 :: 2 :: 3 :: nil) (2 :: nil) D"
    , succeeds "sets.mod" "disjoint (1 :: nil) (2 :: nil)"
    , fails "sets.mod" "disjoint (1 :: nil) (1 :: 2 :: nil)"
    , succeeds "sets.mod" "insert 1 (2 :: nil) S"
    , succeeds "sets.mod" "card (1 :: 1 :: 2 :: nil) N"
    , succeeds "sets.mod" "seteq (1 :: 2 :: nil) (2 :: 1 :: nil)"
    , succeeds "assoc.mod" "lookup 1 (pr 1 2 :: nil) Y"
    , succeeds "assoc.mod" "update 1 9 (pr 1 2 :: nil) L"
    , succeeds "assoc.mod" "delassoc 1 (pr 1 2 :: pr 3 4 :: nil) L"
    , succeeds "prenex.mod" "nnf (neg (and (atom a) (atom a))) D"
    , succeeds "prenex.mod" "nnf (neg (all (x\\ atom x))) D"
    , succeeds "hoas_lambda.mod" "subst (x\\ x) (abs (y\\ y)) M"
    , succeeds "hoas_lambda.mod" "beta (app (abs (x\\ x)) (abs (y\\ y))) M"
    , succeeds "typeinf.mod" "of (app (abs (x\\ x)) c) i"
    , succeeds "typeinf.mod" "of c i"
    , succeeds "trees.mod" "tmember 2 (node 1 empty (node 2 empty empty))"
    , succeeds "trees.mod" "tsize (node 1 empty empty) N"
    , succeeds "trees.mod" "tflatten (node 2 (node 1 empty empty) empty) L"
    , succeeds "trees.mod" "tmap (x\\ x) (node 1 empty empty) T"
    , succeeds "strings.mod" "strcat \"ab\" \"cd\" S"
    , succeeds "strings.mod" "empty_string \"\""
    ]
  where
    succeeds file q = testCase (file ++ " ⊢ " ++ q) $ do
      sols <- runEx file q
      assertBool "expected success" (not (null sols))
    fails file q = testCase (file ++ " ⊬ " ++ q) $ do
      sols <- runEx file q
      assertBool "expected failure" (null sols)
    nsols file q n = testCase (file ++ " # " ++ q) $ do
      sols <- runEx file q
      assertEqual "solution count" n (length sols)

    runEx file q = do
      r <- loadFile ["examples", "."] ("examples/" ++ file)
      case r of
        Left e -> fail (T.unpack (renderError e))
        Right ld ->
          case runQueryText ld (T.pack q) of
            Left e -> fail (T.unpack (renderError e))
            Right sols -> pure sols

