-- | Simple-type helpers.
module Kernel.TypeSpec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import LambdaProlog.Kernel.Kind (Kind (..), kindArity)
import LambdaProlog.Kernel.Type
  ( Type (..)
  , substTyGen
  , tyArgs
  , tyArity
  , tyArrs
  )
import LambdaProlog.Name (emptyInterner, internMany)

tests :: TestTree
tests =
  testGroup
    "kernel.type"
    [ testCase "kind arity of list" $
        assertEqual "" 1 (kindArity (KArr KType KType))
    , testCase "tyArrs / tyArgs round-trip" $
        assertEqual "" ([tyInt, tyListInt], tyO) (tyArgs listFn)
    , testCase "tyArity counts arrows" $
        assertEqual "" 2 (tyArity listFn)
    , testCase "substTyGen instantiates a scheme body" $
        -- ∀A. A -> list A  instantiated at int
        let body = TyArr (TyGen 0) (TyCon listN [TyGen 0])
            inst = substTyGen [tyInt] body
            expected = TyArr tyInt tyListInt
         in assertEqual "" expected inst
    ]
  where
    (ns, _intern) = internMany ["o", "int", "list"] emptyInterner
    oN = ns !! 0
    intN = ns !! 1
    listN = ns !! 2
    tyO = TyCon oN []
    tyInt = TyCon intN []
    tyListInt = TyCon listN [tyInt]
    listFn = tyArrs [tyInt, tyListInt] tyO
