-- | Tasty test suite.
module Main (main) where

import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main =
  defaultMain $
    testGroup
      "lambda-prolog"
      [ -- [TODO]: test trees
      ]
