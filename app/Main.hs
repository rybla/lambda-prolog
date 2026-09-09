-- | Implements a CLI for running lambda-prolog programs and interacting with them.
module Main (main) where

import LambdaProlog.Cli qualified

main :: IO ()
main = LambdaProlog.Cli.main
