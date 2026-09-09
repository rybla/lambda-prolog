-- | Tasty test suite.
module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import Kernel.PrettySpec qualified
import Kernel.SearchSpec qualified
import Kernel.TermSpec qualified
import Kernel.TypeSpec qualified
import Kernel.UnifySpec qualified
import Examples.ExamplesSpec qualified
import Surface.ElabSpec qualified
import Surface.ParseSpec qualified

main :: IO ()
main =
  defaultMain $
    testGroup
      "lambda-prolog"
      [ Kernel.TermSpec.tests
      , Kernel.TypeSpec.tests
      , Kernel.PrettySpec.tests
      , Kernel.UnifySpec.tests
      , Kernel.SearchSpec.tests
      , Surface.ParseSpec.tests
      , Surface.ElabSpec.tests
      , Examples.ExamplesSpec.tests
      ]
