-- | Elaboration and end-to-end query tests on small source strings.
module Surface.ElabSpec (tests) where

import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Driver (loadFile, loadSource, runQueryText)
import LambdaProlog.Kernel.Search (Solution (..))
import LambdaProlog.Kernel.Term (intLit, stringLit)

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
    , testCase "anonymous wildcard is a distinct variable" $
        -- `_` in a clause head must not be rejected as unbound.
        case loadSource "w.mod" wildSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "p 1 X" of
              Left e -> fail (show e)
              Right sols -> assertBool "succeeds" (not (null sols))
    , testCase "is evaluates addition" $
        case loadSource "arith.mod" "module arith.\n" of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "N is 1 + 2" of
              Left e -> fail (show e)
              Right sols -> do
                assertEqual "one" 1 (length sols)
                assertEqual "3" (Just (intLit 3)) (IntMap.lookup 0 (solBinds (sols !! 0)))
    , testCase "integer comparison as a goal" $
        case loadSource "cmp.mod" "module cmp.\n" of
          Left e -> fail (show e)
          Right ld -> do
            case runQueryText ld "3 > 1" of
              Left e -> fail (show e)
              Right sols -> assertBool "3>1" (not (null sols))
            case runQueryText ld "1 > 3" of
              Left e -> fail (show e)
              Right sols -> assertBool "1>3 fails" (null sols)
    , testCase "true as a higher-order goal argument" $
        -- once G :- G, !.  Instantiating G with the constant true must succeed.
        case loadSource "once.mod" onceSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "once true" of
              Left e -> fail (show e)
              Right sols -> assertBool "once true" (not (null sols))
    , testCase "HOAS query with a lowercase binder" $
        case loadSource "abs.mod" absSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "eval (abs (x\\ x)) V" of
              Left e -> fail (show e)
              Right sols -> assertBool "eval id" (not (null sols))
    , testCase "string concatenation via is" $
        case loadSource "str.mod" "module str.\n" of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "S is \"ab\" ^ \"cd\"" of
              Left e -> fail (show e)
              Right sols ->
                assertEqual
                  "abcd"
                  (Just (stringLit "abcd"))
                  (IntMap.lookup 0 (solBinds (sols !! 0)))
    , testCase "once of a conjunction succeeds" $
        -- The argument is elaborated as a term; search must reread ',' as ∧.
        case loadSource "once.mod" onceSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "once (true, true)" of
              Left e -> fail (show e)
              Right sols -> assertBool "once (true, true)" (not (null sols))
    , testCase "once of a failing conjunction fails" $
        case loadSource "once.mod" onceSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "once (fail, true)" of
              Left e -> fail (show e)
              Right sols -> assertBool "once (fail, true)" (null sols)
    , testCase "n-ary pi binders (nested lambdas)" $
        case loadSource "nary.mod" narySrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "pi x\\ y\\ ident x x" of
              Left e -> fail (show e)
              Right sols -> assertBool "pi x\\ y\\" (not (null sols))
    , testCase "n-ary pi binders (ELPI-style juxtaposition)" $
        -- `pi x y\\ G` is `pi x\\ pi y\\ G`.
        case loadSource "nary.mod" narySrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "pi x y\\ ident x x" of
              Left e -> fail (show e)
              Right sols -> assertBool "pi x y\\" (not (null sols))
    , testCase "n-ary sigma binders" $
        case loadSource "nary.mod" narySrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "sigma X Y\\ ident X X, Y = 1" of
              Left e -> fail (show e)
              Right sols -> assertBool "sigma X Y\\" (not (null sols))
    , testCase "once of a universal goal" $
        case loadSource "nary.mod" narySrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "once (pi x\\ ident x x)" of
              Left e -> fail (show e)
              Right sols -> assertBool "once pi" (not (null sols))
    , testCase "HOAS scope escape via foreign meta fails" $
        case loadSource "abs.mod" absSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "sigma M\\ pi x\\ sigma Z\\ M = abs (w\\ Z), Z = x" of
              Left e -> fail (show e)
              Right sols -> assertBool "no escape" (null sols)
    , testCase "eigenvariable cannot unify with program constant" $
        case loadSource "lists.mod" listsSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "pi x\\ x = append" of
              Left e -> fail (show e)
              Right sols -> assertBool "no collision" (null sols)
    , testCase "level pops after universal goal" $
        case loadSource "nary.mod" narySrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "(pi x\\ ident x x), (pi y\\ Y = y)" of
              Left e -> fail (show e)
              Right sols -> assertBool "cannot escape" (null sols)
    , testCase "hypothetical clause preserves query variable binding" $
        case loadSource "hyp.mod" hypSrc of
          Left e -> fail (show e)
          Right ld -> do
            case runQueryText ld "Key = 1, (edge Key 999 => edge 1 Y)" of
              Left e -> fail (show e)
              Right sols -> do
                assertEqual "one sol" 1 (length sols)
                assertEqual "Y = 999" (Just (intLit 999)) (IntMap.lookup 1 (solBinds (head sols)))
            case runQueryText ld "Key = 1, (edge Key 999 => edge 2 Y)" of
              Left e -> fail (show e)
              Right sols -> assertBool "fails" (null sols)
    , testCase "sibling hypothetical clauses isolate local meta variables" $
        case loadSource "hyp.mod" hypSrc of
          Left e -> fail (show e)
          Right ld ->
            case runQueryText ld "(edge 1 2, edge 2 3) => (edge 1 A, edge 2 B)" of
              Left e -> fail (show e)
              Right sols -> do
                assertEqual "one sol" 1 (length sols)
                assertEqual "A = 2" (Just (intLit 2)) (IntMap.lookup 0 (solBinds (head sols)))
                assertEqual "B = 3" (Just (intLit 3)) (IntMap.lookup 1 (solBinds (head sols)))
    ]
  where
    wildSrc :: Text
    wildSrc =
      "module w.\n\
      \type p int -> int -> o.\n\
      \p _ X.\n"
    onceSrc :: Text
    onceSrc =
      "module once.\n\
      \type once o -> o.\n\
      \once G :- G, !.\n"
    absSrc :: Text
    absSrc =
      "module absmod.\n\
      \kind tm type.\n\
      \type app tm -> tm -> tm.\n\
      \type abs (tm -> tm) -> tm.\n\
      \type eval tm -> tm -> o.\n\
      \eval (app M N) V :- eval M (abs R), eval N U, eval (R U) V.\n\
      \eval (abs R) (abs R).\n\
      \type copy tm -> tm -> o.\n\
      \copy (abs R) (abs S) :- pi x\\ copy x x => copy (R x) (S x).\n\
      \type size tm -> int -> o.\n\
      \size (abs R) K :- pi x\\ size x 1 => size (R x) N, K is N + 1.\n"
    listsSrc :: Text
    listsSrc =
      "module lists.\n\
      \type append list A -> list A -> list A -> o.\n\
      \append nil L L.\n\
      \append (X :: L) K (X :: M) :- append L K M.\n"
    narySrc :: Text
    narySrc =
      "module nary.\n\
      \type ident A -> A -> o.\n\
      \ident X X.\n\
      \type once o -> o.\n\
      \once G :- G, !.\n"
    hypSrc :: Text
    hypSrc =
      "module hyp.\n\
      \type edge int -> int -> o.\n\
      \type ident A -> A -> o.\n\
      \ident X X.\n"
