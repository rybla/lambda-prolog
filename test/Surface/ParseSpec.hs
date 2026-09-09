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
    ]
  where
    seqLen (SSeq _ xs) = length xs
    seqLen _ = 1
    isApp SApp {} = True
    isApp _ = False
    listsFrag :: Text
    listsFrag =
      "module lists.\n\
      \type append list A -> list A -> list A -> o.\n\
      \append nil L L.\n\
      \append (X::L) K (X::M) :- append L K M.\n"
