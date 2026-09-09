-- | Uniform proof search for higher-order hereditary Harrop goals.
--
-- Depth-first, left-to-right, clause-order, with a trail. The current fail
-- continuation lives in a register so cut can redirect it (Prolog cut:
-- trim remaining clauses of the enclosing atomic call).
module LambdaProlog.Kernel.Search
  ( Solution (..)
  , query
  , queryN
  ) where

import Control.Monad.ST (ST)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import Data.Text qualified as T

import LambdaProlog.Kernel.Builtin (evalArith)
import LambdaProlog.Kernel.Goal
  ( Clause (..)
  , Goal (..)
  , Program
  , addHyps
  , copyClause
  , lookupClauses
  )

import LambdaProlog.Kernel.Trail
  ( Trail
  , allocMeta
  , freshMeta
  , mark
  , pushLevel
  , registerEigen
  , runTrail
  , unwind
  )
import LambdaProlog.Kernel.Term
  ( Head (..)
  , Level (..)
  , MetaId (..)
  , Term (..)
  , intLit
  , meta
  )
import LambdaProlog.Kernel.Unify (derefNf, unify, whnf)
import LambdaProlog.Name (Interner, Name, intern)
import LambdaProlog.Prelude (Builtins (..), prelude)

data Solution = Solution
  { solBinds :: IntMap Term
  }
  deriving stock (Eq, Show)

data Env s = Env
  { envTrail :: Trail s
  , envProg :: STRef s Program
  , envIntern :: STRef s Interner
  , envFail :: STRef s (ST s ())
  , envCut :: STRef s (ST s ())
  , envEigenN :: STRef s Int
  }

query :: Program -> [MetaId] -> Goal -> [Solution]
query = queryN maxBound

queryN :: Int -> Program -> [MetaId] -> Goal -> [Solution]
queryN maxN prog qvars g =
  runTrail $ \tr -> do
    mapM_ (\m -> allocMeta tr m (Level 0) Nothing) qvars
    acc <- newSTRef ([] :: [Solution])
    nref <- newSTRef (0 :: Int)
    progR <- newSTRef prog
    internR <- newSTRef (bInterner prelude)
    done <- pure (pure () :: ST s ())
    failR <- newSTRef done
    cutR <- newSTRef done
    eigenN <- newSTRef (0 :: Int)
    let env = Env tr progR internR failR cutR eigenN
        sc = do
          n <- readSTRef nref
          if n >= maxN
            then pure ()
            else do
              sol <- freeze tr qvars
              xs <- readSTRef acc
              writeSTRef acc (xs ++ [sol])
              writeSTRef nref (n + 1)
              invokeFail env
    solve env g sc
    readSTRef acc

invokeFail :: Env s -> ST s ()
invokeFail env = do
  fc <- readSTRef (envFail env)
  fc

solve :: Env s -> Goal -> ST s () -> ST s ()
solve env g sc = case g of
  GTrue -> sc
  GFail -> invokeFail env
  GCut -> do
    atomFail <- readSTRef (envCut env)
    writeSTRef (envFail env) atomFail
    sc
  GAtom p ts -> solveAtom env p ts sc
  GFlex m ts -> solveFlex env m ts sc
  GAnd a b -> solve env a (solve env b sc)
  GOr a b -> do
    let tr = envTrail env
    old <- readSTRef (envFail env)
    m <- mark tr
    writeSTRef
      (envFail env)
      (unwind tr m >> writeSTRef (envFail env) old >> solve env b sc)
    solve env a sc
  GExists _ty k -> do
    mv <- freshMeta (envTrail env) Nothing
    solve env (k (meta mv)) sc
  GForall _ty k -> solveForall env k sc
  GImpl cs b -> solveImpl env cs b sc
  GEq a b -> solveUnify env a b sc
  GIs lhs rhs -> solveIs env lhs rhs sc
  GNot g' -> solveNot env g' sc

solveAtom :: Env s -> Name -> [Term] -> ST s () -> ST s ()
solveAtom env p ts sc = do
  prog <- readSTRef (envProg env)
  let cs = lookupClauses p prog
  oldFail <- readSTRef (envFail env)
  oldCut <- readSTRef (envCut env)
  -- Cut jumps to the fail of this atom (no more clauses).
  let atomFail = writeSTRef (envFail env) oldFail >> writeSTRef (envCut env) oldCut >> oldFail
  writeSTRef (envCut env) atomFail
  tryCs atomFail oldFail oldCut cs
  where
    tr = envTrail env
    tryCs atomFail _oldFail _oldCut [] = atomFail
    tryCs atomFail oldFail oldCut (c : rest) = do
      m <- mark tr
      writeSTRef
        (envFail env)
        (unwind tr m >> tryCs atomFail oldFail oldCut rest)
      c' <- copyClause tr c
      let headT = TApp (HConst (clPred c')) (clArgs c')
          goalT = TApp (HConst p) ts
      r <- unify tr headT goalT
      case r of
        Left _ -> invokeFail env
        Right () ->
          -- Cut inside the body still refers to this atom. Restore the
          -- outer cut only after the body succeeds.
          solve env (clBody c') $ do
            writeSTRef (envCut env) oldCut
            sc

solveForall :: Env s -> (Term -> Goal) -> ST s () -> ST s ()
solveForall env k sc = do
  let tr = envTrail env
  old <- readSTRef (envFail env)
  m <- mark tr
  writeSTRef
    (envFail env)
    (unwind tr m >> writeSTRef (envFail env) old >> old)
  _ <- pushLevel tr
  e <- internEigen env
  registerEigen tr e
  solve env (k (TApp (HConst e) [])) sc

internEigen :: Env s -> ST s Name
internEigen env = do
  n <- readSTRef (envEigenN env)
  writeSTRef (envEigenN env) (n + 1)
  internR <- readSTRef (envIntern env)
  let (nm, intern') = intern ("#e" <> T.pack (show n)) internR
  writeSTRef (envIntern env) intern'
  pure nm

solveImpl :: Env s -> [Clause] -> Goal -> ST s () -> ST s ()
solveImpl env cs g sc = do
  let tr = envTrail env
  oldFail <- readSTRef (envFail env)
  m <- mark tr
  oldP <- readSTRef (envProg env)
  writeSTRef (envProg env) (addHyps cs oldP)
  let leave =
        writeSTRef (envProg env) oldP
          >> unwind tr m
          >> writeSTRef (envFail env) oldFail
          >> oldFail
  writeSTRef (envFail env) leave
  solve env g $ do
    -- Body succeeded: drop hypotheticals for the continuation, but put
    -- them back if we are asked for more solutions of the body.
    writeSTRef (envProg env) oldP
    innerFail <- readSTRef (envFail env)
    writeSTRef
      (envFail env)
      (writeSTRef (envProg env) (addHyps cs oldP) >> innerFail)
    sc

solveUnify :: Env s -> Term -> Term -> ST s () -> ST s ()
solveUnify env a b sc = do
  let tr = envTrail env
  old <- readSTRef (envFail env)
  m <- mark tr
  r <- unify tr a b
  case r of
    Left _ -> unwind tr m >> invokeFail env
    Right () -> do
      writeSTRef
        (envFail env)
        (unwind tr m >> writeSTRef (envFail env) old >> old)
      sc

solveIs :: Env s -> Term -> Term -> ST s () -> ST s ()
solveIs env lhs rhs sc = do
  rhs' <- derefNf (envTrail env) rhs
  case evalArith rhs' of
    Nothing -> invokeFail env
    Just n -> solveUnify env lhs (intLit n) sc

solveNot :: Env s -> Goal -> ST s () -> ST s ()
solveNot env g sc = do
  let tr = envTrail env
  m <- mark tr
  found <- newSTRef False
  oldFail <- readSTRef (envFail env)
  oldCut <- readSTRef (envCut env)
  -- Run g with a private fail that just returns, and a success that flags.
  writeSTRef (envFail env) (pure ())
  writeSTRef (envCut env) (pure ())
  solve env g (writeSTRef found True)
  writeSTRef (envFail env) oldFail
  writeSTRef (envCut env) oldCut
  unwind tr m
  hit <- readSTRef found
  if hit then invokeFail env else sc

solveFlex :: Env s -> MetaId -> [Term] -> ST s () -> ST s ()
solveFlex env m ts sc = do
  t <- whnf (envTrail env) (TApp (HMeta m) ts)
  case t of
    TApp (HConst p) ts' -> solveAtom env p ts' sc
    TApp (HMeta _) _ -> invokeFail env
    _ -> invokeFail env

freeze :: Trail s -> [MetaId] -> ST s Solution
freeze tr qvars = do
  pairs <- mapM (\mid -> (metaInt mid,) <$> derefNf tr (meta mid)) qvars
  pure (Solution (IntMap.fromList pairs))
