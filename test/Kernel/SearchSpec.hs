-- | Uniform proof-search tests: Horn, implication, pi, cut, builtins.
module Kernel.SearchSpec (tests) where

import Data.IntMap.Strict qualified as IntMap
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Kernel.Goal
  ( Clause (..)
  , Goal (..)
  , Program
  , consultClauses
  , emptyProgram
  , mkClause
  )
import LambdaProlog.Kernel.Search (Solution (..), query, queryN)
import LambdaProlog.Kernel.Term
  ( MetaId (..)
  , Term
  , apps
  , con
  , intLit
  , meta
  )
import LambdaProlog.Name (internMany)
import LambdaProlog.Prelude
  ( Builtins (..)
  , prelude
  , tyO
  )

tests :: TestTree
tests =
  testGroup
    "kernel.search"
    [ testCase "true succeeds" $
        assertBool "true" (sat emptyProgram GTrue)
    , testCase "fail fails" $
        assertBool "fail" (not (sat emptyProgram GFail))
    , testCase "conjunction" $
        assertBool "true, true" (sat emptyProgram (GAnd GTrue GTrue))
    , testCase "disjunction" $
        assertBool "fail; true" (sat emptyProgram (GOr GFail GTrue))
    , testCase "append [1,2] [3] [1,2,3]" $
        assertBool "append" $
          sat appendProg $
            GAtom ap [list [n1, n2], list [n3], list [n1, n2, n3]]
    , testCase "append [1,2] [3] L  binds L" $
        let sols = query appendProg [MetaId 0] $
              GAtom ap [list [n1, n2], list [n3], x0]
         in assertEqual "one solution" 1 (length sols)
              >> assertEqual
                "L"
                (Just (list [n1, n2, n3]))
                (IntMap.lookup 0 (solBinds (sols !! 0)))
    , testCase "append split has several solutions" $
        let sols = query appendProg [MetaId 0, MetaId 1] $
              GAtom ap [x0, x1, list [n1, n2]]
         in assertEqual "3 splits" 3 (length sols)
    , testCase "implication adds a fact" $
        assertBool "p a => p a" $
          sat emptyProgram $
            GImpl [fact p [a]] (GAtom p [a])
    , testCase "implication is scoped" $
        assertBool "does not leak" $
          not $
            sat emptyProgram $
              GAnd (GImpl [fact p [a]] GTrue) (GAtom p [a])
    , testCase "pi x\\ x = x" $
        assertBool "refl" $
          sat emptyProgram (GForall tyO (\e -> GEq e e))
    , testCase "pi x\\ X = x  fails to escape" $
        assertBool "no escape" $
          null $
            query emptyProgram [MetaId 0] (GForall tyO (\e -> GEq x0 e))
    , testCase "sigma Y\\ pi z\\ Y = z  fails to escape" $
        assertBool "no escape sigma" $
          null $
            query emptyProgram [] (GExists tyO (\y -> GForall tyO (\z -> GEq y z)))
    , testCase "pi x\\ F x = x  binds F to id" $
        let sols =
              query emptyProgram [MetaId 0] $
                GForall tyO (\e -> GEq (apps x0 [e]) e)
         in assertEqual "one" 1 (length sols)
    , testCase "hidden reverse via sigma + =>" $
        assertBool "reverse" $
          sat emptyProgram hiddenReverseGoal
    , testCase "cut keeps a single member solution" $
        let sols =
              query memberCutProg [MetaId 0] $
                GAtom memb [x0, list [n1, n1]]
         in assertEqual "cut" 1 (length sols)
    , testCase "member without cut has two solutions" $
        let sols =
              query memberProg [MetaId 0] $
                GAtom memb [x0, list [n1, n1]]
         in assertEqual "no cut" 2 (length sols)
    , testCase "is 1+2" $
        let sols = query emptyProgram [MetaId 0] $
              GIs x0 (apps (con (bPlus prelude)) [intLit 1, intLit 2])
         in assertEqual "3" (Just (intLit 3)) (IntMap.lookup 0 (solBinds (sols !! 0)))
    , testCase "not fail succeeds" $
        assertBool "not fail" (sat emptyProgram (GNot GFail))
    , testCase "not true fails" $
        assertBool "not true" (not (sat emptyProgram (GNot GTrue)))
    , testCase "queryN caps solutions" $
        let sols = queryN 2 appendProg [MetaId 0, MetaId 1] $
              GAtom ap [x0, x1, list [n1, n2]]
         in assertEqual "capped" 2 (length sols)
    , testCase "conjunction term is solved as a goal" $
        -- once (true, true) elaborates the argument as a term headed by ','.
        assertBool "true, true" $
          sat emptyProgram $
            GAtom (bAnd b) [con (bTrue b), con (bTrue b)]
    , testCase "conjunction term fails if a conjunct fails" $
        assertBool "fail, true" $
          not $
            sat emptyProgram $
              GAtom (bAnd b) [con (bFail b), con (bTrue b)]
    , testCase "disjunction term is solved as a goal" $
        assertBool "fail; true" $
          sat emptyProgram $
            GAtom (bOr b) [con (bFail b), con (bTrue b)]
    ]
  where
    b = prelude
    intern0 = bInterner b
    (extra, _intern) = internMany ["append", "member", "p", "a", "rv"] intern0
    appendN = extra !! 0
    memb = extra !! 1
    p = extra !! 2
    aN = extra !! 3
    rv = extra !! 4
    ap = appendN
    a = con aN
    n1 = intLit 1
    n2 = intLit 2
    n3 = intLit 3
    x0 = meta (MetaId 0)
    x1 = meta (MetaId 1)
    nil = con (bNil b)
    cons x y = apps (con (bCons b)) [x, y]
    list = foldr cons nil

    tmp :: Int -> Term
    tmp i = meta (MetaId i)

    fact predN args = mkClause predN 0 args GTrue

    appendProg =
      consultClauses
        [ mkClause appendN 1 [nil, tmp 0, tmp 0] GTrue
        , mkClause
            appendN
            4
            [cons (tmp 0) (tmp 1), tmp 2, cons (tmp 0) (tmp 3)]
            (GAtom appendN [tmp 1, tmp 2, tmp 3])
        ]
        emptyProgram

    memberProg =
      consultClauses
        [ mkClause memb 2 [tmp 0, cons (tmp 0) (tmp 1)] GTrue
        , mkClause
            memb
            3
            [tmp 0, cons (tmp 1) (tmp 2)]
            (GAtom memb [tmp 0, tmp 2])
        ]
        emptyProgram

    memberCutProg =
      consultClauses
        [ mkClause memb 2 [tmp 0, cons (tmp 0) (tmp 1)] GCut
        , mkClause
            memb
            3
            [tmp 0, cons (tmp 1) (tmp 2)]
            (GAtom memb [tmp 0, tmp 2])
        ]
        emptyProgram

    hiddenReverseGoal =
      let l = list [n1, n2, n3]
          k = list [n3, n2, n1]
          cNil = mkClause rv 1 [nil, tmp 0, tmp 0] GTrue
          cCons =
            mkClause
              rv
              4
              [cons (tmp 0) (tmp 1), tmp 2, tmp 3]
              (GAtom rv [tmp 1, cons (tmp 0) (tmp 2), tmp 3])
       in GImpl [cNil, cCons] (GAtom rv [l, nil, k])

sat :: Program -> Goal -> Bool
sat prog g = not (null (query prog [] g))
