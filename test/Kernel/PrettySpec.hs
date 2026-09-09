-- | Pretty-printing of types and terms, including list sugar.
module Kernel.PrettySpec (tests) where

import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import LambdaProlog.Kernel.Kind (Kind (..))
import LambdaProlog.Kernel.Pretty
  ( mkPrintEnv
  , renderKind
  , renderTerm
  , renderType
  )
import LambdaProlog.Kernel.Term
  ( MetaId (..)
  , apps
  , con
  , intLit
  , lam
  , lams
  , meta
  , stringLit
  , var
  )
import LambdaProlog.Kernel.Type (Type (..), tyArrs)
import LambdaProlog.Name (emptyInterner, internMany)

tests :: TestTree
tests =
  testGroup
    "kernel.pretty"
    [ testCase "kind type" $
        assertEqual "" ("type" :: Text) (renderKind KType)
    , testCase "kind of list" $
        assertEqual "" ("type -> type" :: Text) (renderKind (KArr KType KType))
    , testCase "arrow type associates right" $
        assertEqual "" ("int -> list int -> o" :: Text) (renderType env listFn)
    , testCase "arrow on the left is parenthesized" $
        assertEqual
          ""
          ("(int -> int) -> o" :: Text)
          (renderType env (TyArr (TyArr tyInt tyInt) tyO))
    , testCase "identity λ" $
        assertEqual "" ("x\\ x" :: Text) (renderTerm env (lam (var 0)))
    , testCase "K combinator" $
        assertEqual "" ("x\\ y\\ x" :: Text) (renderTerm env (lams 2 (var 1)))
    , testCase "application" $
        assertEqual "" ("f a b" :: Text) (renderTerm env (apps f [a, b]))
    , testCase "nested application is parenthesized" $
        assertEqual "" ("f (g a)" :: Text) (renderTerm env (apps f [apps g [a]]))
    , testCase "empty list" $
        assertEqual "" ("[]" :: Text) (renderTerm env (con nilN))
    , testCase "proper list" $
        assertEqual
          ""
          ("[1, 2, 3]" :: Text)
          (renderTerm env (cons (intLit 1) (cons (intLit 2) (cons (intLit 3) (con nilN)))))
    , testCase "cons with a variable tail" $
        assertEqual
          ""
          ("[1 | xs]" :: Text)
          (renderTerm env (cons (intLit 1) (con xsN)))
    , testCase "string literal" $
        assertEqual "" ("\"hi\"" :: Text) (renderTerm env (stringLit "hi"))
    , testCase "meta" $
        assertEqual "" ("X0" :: Text) (renderTerm env (meta (MetaId 0)))
    ]
  where
    names = ["o", "int", "string", "list", "nil", "::", "f", "g", "a", "b", "xs"]
    (ns, intern) = internMany names emptyInterner
    oN = ns !! 0
    intN = ns !! 1
    listN = ns !! 3
    nilN = ns !! 4
    consN = ns !! 5
    fN = ns !! 6
    gN = ns !! 7
    aN = ns !! 8
    bN = ns !! 9
    xsN = ns !! 10
    env = mkPrintEnv intern
    tyO = TyCon oN []
    tyInt = TyCon intN []
    tyListInt = TyCon listN [tyInt]
    listFn = tyArrs [tyInt, tyListInt] tyO
    f = con fN
    g = con gN
    a = con aN
    b = con bN
    cons x xs = apps (con consN) [x, xs]