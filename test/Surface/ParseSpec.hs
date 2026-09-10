-- | Parser and mixfix tests.
module Surface.ParseSpec (tests) where

import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Surface.Fixity (defaultOps, mixfixTerm)
import LambdaProlog.Surface.Parser (parseModule, parseTerm)
import LambdaProlog.Surface.Syntax

tests :: TestTree
tests =
  testGroup
    "surface.parse"
    [ testCase "parse append clauses" $
        case parseTerm "-" "append nil L L" of
          Left e -> fail (show e)
          Right t ->
            assertEqual "seq length" 4 (seqLen t)
    , testCase "parse lambda" $
        case parseTerm "-" "x\\ x" of
          Left e -> fail (show e)
          Right SLam {} -> pure ()
          Right t -> fail ("expected lambda, got " ++ show t)
    , testCase "parse list" $
        case parseTerm "-" "[1, 2, 3]" of
          Left e -> fail (show e)
          Right (SList _ es Nothing) -> assertEqual "3 elems" 3 (length es)
          Right t -> fail ("expected list, got " ++ show t)
    , testCase "mixfix cons" $
        case parseTerm "-" "X :: L" of
          Left e -> fail (show e)
          Right t ->
            case mixfixTerm defaultOps t of
              Left e -> fail (show e)
              Right t' -> assertBool "is app" (isApp t')
    , testCase "mixfix clause neck" $
        case parseTerm "-" "p X :- q X, r X" of
          Left e -> fail (show e)
          Right t ->
            case mixfixTerm defaultOps t of
              Left e -> fail (show e)
              Right t' -> assertBool "resolved" (isApp t')
    , testCase "parse lists.mod fragment" $
        case parseModule "lists.mod" listsFrag of
          Left e -> fail (show e)
          Right m -> do
            assertEqual "name" ("lists" :: Text) (identName (modName m))
            assertBool "has decls" (not (null (modDecls m)))
    , testCase "colon-dash is not a typed lambda" $
        -- `K :- pi x\ G` used to parse as `K : -pi x \ G`.
        case parseTerm "-" "p K :- pi x\\ q" of
          Left e -> fail (show e)
          Right t ->
            case mixfixTerm defaultOps t of
              Left e -> fail (show e)
              Right t' -> assertBool "uses :-" (hasNeck t')
    , testCase "nested lambdas" $
        case parseTerm "-" "x\\ y\\ x" of
          Left e -> fail (show e)
          Right (SLam _ x _ (SLam _ y _ _)) -> do
            assertEqual "outer" ("x" :: Text) (identName x)
            assertEqual "inner" ("y" :: Text) (identName y)
          Right t -> fail ("expected nested lambdas, got " ++ show t)
    , testCase "caret is a symbolic identifier" $
        case parseTerm "-" "S is \"ab\" ^ \"cd\"" of
          Left e -> fail (show e)
          Right t ->
            case mixfixTerm defaultOps t of
              Left e -> fail (show e)
              Right t' -> assertBool "resolved" (isApp t')
    , testCase "parse query command variants" $ do
        let src = "module q.\n\
                  \query ? true.\n\
                  \query succeeds ? true.\n\
                  \query fails ? fail.\n\
                  \query sample(3) ? true.\n\
                  \query [succeeds, sample(2)] ? true.\n\
                  \query succeeds sample(5) ? true.\n"
        case parseModule "q.mod" src of
          Left e -> fail (show e)
          Right m -> do
            let decls = modDecls m
            assertEqual "6 query decls" 6 (length decls)
            case decls of
              [ DQuery [] _
                , DQuery [QOSucceeds] _
                , DQuery [QOFails] _
                , DQuery [QOSample 3] _
                , DQuery [QOSucceeds, QOSample 2] _
                , DQuery [QOSucceeds, QOSample 5] _
                ] -> pure ()
              other -> fail ("unexpected parsed decls: " ++ show other)
    ]
  where
    seqLen (SSeq _ xs) = length xs
    seqLen _ = 1
    isApp SApp {} = True
    isApp _ = False
    hasNeck t = case t of
      SApp _ (SApp _ (SId i) _) _ -> identName i == ":-"
      SApp _ a _ -> hasNeck a
      _ -> False
    listsFrag :: Text
    listsFrag =
      "module lists.\n\
      \type append list A -> list A -> list A -> o.\n\
      \append nil L L.\n\
      \append (X::L) K (X::M) :- append L K M.\n"
