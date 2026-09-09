-- | Substitution, β-reduction, and η-expansion tests.
module Kernel.TermSpec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import LambdaProlog.Kernel.Subst (betaNf, etaExpand)
import LambdaProlog.Kernel.Term
  ( app
  , apps
  , con
  , instantiate
  , lam
  , lams
  , shift
  , unLams
  , var
  )
import LambdaProlog.Name (emptyInterner, internMany)

tests :: TestTree
tests =
  testGroup
    "kernel.term"
    [ testCase "identity β-reduces" $
        assertEqual "" a (app (lam (var 0)) a)
    , testCase "K combinator" $
        assertEqual "" a (apps (lams 2 (var 1)) [a, b])
    , testCase "nested instantiate" $
        -- (λx. λy. x) a  ==>  λy. a
        assertEqual "" (lam a) (app (lams 2 (var 1)) a)
    , testCase "apply under remaining λ" $
        -- (λx. λy. y x) a b  ==>  b a
        assertEqual
          ""
          (apps b [a])
          (apps (lams 2 (app (var 0) (var 1))) [a, b])
    , testCase "shift of a closed term is identity" $
        assertEqual "" tClosed (shift 5 0 tClosed)
    , testCase "shift raises a free index" $
        assertEqual "" (var 3) (shift 2 1 (var 1))
    , testCase "shift does not touch inner binders" $
        assertEqual "" (lam (var 0)) (shift 4 0 (lam (var 0)))
    , testCase "instantiate under an extra λ" $
        -- body of λx. λy. x  is  λy. x=1; instantiate a for x
        assertEqual "" (lam a) (instantiate a (lam (var 1)))
    , testCase "unLams counts binders" $
        assertEqual "" (2, var 0) (unLams (lams 2 (var 0)))
    , testCase "betaNf is identity on spines" $
        assertEqual "" tClosed (betaNf tClosed)
    , testCase "η-expand a constant to arity 2" $
        -- λx. λy. a y x   (args are 1 then 0)
        let expected = lams 2 (apps a [var 1, var 0])
         in assertEqual "" expected (etaExpand 2 a)
    , testCase "η-expand 0 is identity" $
        assertEqual "" a (etaExpand 0 a)
    ]
  where
    (ns, _intern) = internMany ["a", "b"] emptyInterner
    a = con (ns !! 0)
    b = con (ns !! 1)
    tClosed = apps a [b]
