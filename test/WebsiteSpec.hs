-- | Semantic highlighting: keywords, types, and comment metadata keys.
module WebsiteSpec (tests) where

import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

import LambdaProlog.Surface.Annotate
  ( Mark (..)
  , Role (..)
  , annotateSource
  , markRole
  , markTip
  )

tests :: TestTree
tests =
  testGroup
    "website.annotate"
    [ testCase "module keyword is marked" $
        assertBool "module" (hasRole RKeyword "module" sample)
    , testCase "kind keyword is marked" $
        assertBool "kind" (hasRole RKeyword "kind" sample)
    , testCase "type keyword is marked" $
        assertBool "type" (hasRole RKeyword "type" sample)
    , testCase "title: metadata key in comments" $
        assertBool "title:" (hasRole RMetaKey "title:" sample)
    , testCase "tags: metadata key in comments" $
        assertBool "tags:" (hasRole RMetaKey "tags:" sample)
    , testCase "summary: metadata key in comments" $
        assertBool "summary:" (hasRole RMetaKey "summary:" sample)
    , testCase "type constructor list is marked" $
        assertBool "list" (hasRole RTypeCon "list" sample)
    , testCase "predicate append is marked" $
        assertBool "append" (hasRole RPredicate "append" sample)
    , testCase "append in a clause is a predicate, not a constant" $
        assertBool "clause append" $
          any
            (\mk -> markRole mk == RPredicate && "append" `T.isInfixOf` markTip mk)
            sample
    , testCase "term constructor pr is not a predicate" $
        assertBool "pr" (hasRole RConst "pr" sample)
    , testCase "type o is marked" $
        assertBool "o" (hasRole RTypeCon "o" sample)
    , testCase "type variable A is marked" $
        assertBool "A" (hasRole RTyVar "A" sample)
    , testCase "kind type is marked" $
        assertBool "kind type" (hasRole RKindStar "type" sample)
    , testCase "function type arrow is marked" $
        assertBool "->" (hasRole RPunct "->" sample)
    , testCase "clause terminator is marked" $
        assertBool "." (hasRole RPunct "." sample)
    , testCase "lambda backslash is marked" $
        assertBool "\\" (hasRole RPunct "\\" sample)
    , testCase "cons operator is marked" $
        assertBool "::" (hasRole ROperator "::" sample || hasRole RPunct "::" sample)
    , testCase "pi is marked" $
        assertBool "pi" (hasRole RPi "pi" sample)
    , testCase "block-comment metadata key" $
        assertBool "author:" (hasRole RMetaKey "author:" sample)
    , testCase "bound occurrence of a pi binder" $
        let ms =
              annotateSource "b.mod" $
                T.unlines
                  [ "module b."
                  , "type p A -> o."
                  , "p X :- pi x\\ p x."
                  ]
         in assertBool "binder x" (hasRole RBinder "x" ms)
    ]
  where
    sample =
      annotateSource "t.mod" $
        T.unlines
          [ "% title: Lists"
          , "% tags: library, lists"
          , "% summary: A list library."
          , "/* author: test */"
          , "module lists."
          , "kind pair type -> type -> type."
          , "type pr A -> B -> pair A B."
          , "type append list A -> list A -> list A -> o."
          , "append nil L L."
          , "append (X :: L) K M :- pi x\\ append L K M."
          ]

hasRole :: Role -> Text -> [Mark] -> Bool
hasRole role needle marks =
  any
    (\mk -> markRole mk == role && needle `T.isInfixOf` markTip mk)
    marks
