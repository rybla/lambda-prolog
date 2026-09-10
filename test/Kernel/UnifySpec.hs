-- | Higher-order pattern unification.
module Kernel.UnifySpec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import LambdaProlog.Kernel.Term
  ( Level (..)
  , MetaId (..)
  , app
  , apps
  , con
  , lam
  , meta
  , var
  )
import LambdaProlog.Kernel.Trail
  ( allocMeta
  , mark
  , pushLevel
  , registerEigen
  , runTrail
  , unwind
  )
import LambdaProlog.Kernel.Unify
  ( UnifyError (..)
  , derefNf
  , unify
  , unifyPure
  )
import LambdaProlog.Name (emptyInterner, internMany)

tests :: TestTree
tests =
  testGroup
    "kernel.unify"
    [ testCase "first-order: f X = f a" $
        assertSucceeds (apps f [x]) (apps f [a])
    , testCase "first-order clash: f a = f b" $
        assertFailsClash (apps f [a]) (apps f [b])
    , testCase "rigid arity mismatch" $
        case unifyPure (apps f [a]) (apps f [a, b]) of
          Left ArityMismatch -> pure ()
          other -> fail ("expected ArityMismatch, got " ++ show other)
    , testCase "λx. F x = λx. x  (F = id)" $
        assertSucceeds (lam (app x (var 0))) (lam (var 0))
    , testCase "λx. F = λx. x  (scope)" $
        assertFailsScope (lam x) (lam (var 0))
    , testCase "η: F = λx. c x" $
        assertSucceeds x (lam (app c (var 0)))
    , testCase "occur check: X = f X" $
        case unifyPure x (apps f [x]) of
          Left (Occurs _) -> pure ()
          other -> fail ("expected Occurs, got " ++ show other)
    , testCase "flex/flex X = Y" $
        assertSucceeds x y
    , testCase "pattern: λx. F x = λx. g x x" $
        assertSucceeds
          (lam (app x (var 0)))
          (lam (apps g [var 0, var 0]))
    , testCase "non-pattern: F (c X) = t" $
        case unifyPure (apps x [apps c [y]]) a of
          Left (NotPattern _) -> pure ()
          other -> fail ("expected NotPattern, got " ++ show other)
    , testCase "eigen success: F e = e  at the eigen's level" $
        assertBool "sides equal" assertEigenSuccess
    , testCase "eigen escape: F = e  for a younger eigen" $
        assertBool "escaped" assertEigenEscape
    , testCase "trail unwind restores a binding" $
        assertBool "unbound after unwind" assertUnwind
    , testCase "list cons unifies" $
        assertSucceeds (apps consN [x, a]) (apps consN [b, a])
    , testCase "flex-rigid with meta under lambda: X = λy. R y" $ do
        let r = meta (MetaId 1)
            t = lam (app r (var 0))
        assertSucceeds x t
    , testCase "flex-rigid with meta under nested lambdas: X = λf. λx. R f x" $ do
        let r = meta (MetaId 1)
            t = lam (lam (apps r [var 1, var 0]))
        assertSucceeds x t
    , testCase "flex-rigid pruning: meta under lambda mentioning outer variable" $ do
        -- Outer scope has binder 0 (say under an outer lam).
        -- F has pattern [var 0]. R is applied to [local (var 0), outer (var 1)].
        -- F (var 0) = λy. R y (var 1)
        let fMeta = meta (MetaId 0)
            rMeta = meta (MetaId 1)
            outerTerm = lam (app fMeta (var 0))
            rigidTerm = lam (lam (apps rMeta [var 0, var 1]))
        assertSucceeds outerTerm rigidTerm
    , testCase "prune lowers foreign meta level, preventing subsequent eigen capture" $
        assertBool "pruned meta cannot unify with eigen" assertPruneLowersLevel
    ]
  where
    (ns, _intern) = internMany ["f", "a", "b", "c", "g", "nil", "::", "e"] emptyInterner
    fN = ns !! 0
    aN = ns !! 1
    bN = ns !! 2
    cN = ns !! 3
    gN = ns !! 4
    cons = ns !! 6
    eN = ns !! 7
    f = con fN
    a = con aN
    b = con bN
    c = con cN
    g = con gN
    consN = con cons
    x = meta (MetaId 0)
    y = meta (MetaId 1)

    assertSucceeds s t = do
      let r = runTrail $ \tr -> do
            u <- unify tr s t
            case u of
              Left err -> pure (Left err)
              Right () -> do
                s' <- derefNf tr s
                t' <- derefNf tr t
                pure (Right (s', t'))
      case r of
        Left err -> fail ("unify failed: " ++ show err)
        Right (s', t') ->
          assertEqual "dereferenced sides" s' t'

    assertFailsClash s t =
      case unifyPure s t of
        Left (Clash _ _) -> pure ()
        other -> fail ("expected Clash, got " ++ show other)

    assertFailsScope s t =
      case unifyPure s t of
        Left (Scope _) -> pure ()
        other -> fail ("expected Scope, got " ++ show other)

    assertEigenSuccess =
      runTrail $ \tr -> do
        _ <- pushLevel tr
        registerEigen tr eN
        let e = con eN
            ff = meta (MetaId 0)
        u <- unify tr (app ff e) e
        case u of
          Left _ -> pure False
          Right () -> do
            got <- derefNf tr (app ff e)
            want <- derefNf tr e
            pure (got == want)

    assertEigenEscape =
      runTrail $ \tr -> do
        -- Query variable born outside the pi, eigen born inside.
        allocMeta tr (MetaId 0) (Level 0) Nothing
        _ <- pushLevel tr
        registerEigen tr eN
        u <- unify tr (meta (MetaId 0)) (con eN)
        case u of
          Left (Scope _) -> pure True
          _ -> pure False

    assertPruneLowersLevel =
      runTrail $ \tr -> do
        allocMeta tr (MetaId 0) (Level 0) Nothing
        _ <- pushLevel tr
        registerEigen tr eN
        allocMeta tr (MetaId 1) (Level 1) Nothing
        u1 <- unify tr (meta (MetaId 0)) (lam (meta (MetaId 1)))
        case u1 of
          Left _ -> pure False
          Right () -> do
            u2 <- unify tr (meta (MetaId 1)) (con eN)
            case u2 of
              Left (Scope _) -> pure True
              _ -> pure False

    assertUnwind =
      runTrail $ \tr -> do
        m <- mark tr
        u <- unify tr x a
        case u of
          Left _ -> pure False
          Right () -> do
            unwind tr m
            got <- derefNf tr x
            pure (got == x)
