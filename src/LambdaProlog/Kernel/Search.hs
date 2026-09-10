-- | Uniform proof search for higher-order hereditary Harrop goals.
--
-- Depth-first, left-to-right, clause-order, with a trail. The current fail
-- continuation lives in a register so cut can redirect it (Prolog cut:
-- trim remaining clauses of the enclosing atomic call).
module LambdaProlog.Kernel.Search
  ( Solution (..)
  , query
  , queryN
  , queryWithInterner
  , queryNWithInterner
  ) where

import Control.Monad.ST (ST)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import LambdaProlog.Kernel.Builtin (Ground (..), evalCmp, evalGround)
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
  , popLevel
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
  , applySpine
  , intLit
  , meta
  , stringLit
  )
import LambdaProlog.Kernel.Unify (derefNf, unify, whnf)
import LambdaProlog.Name (Interner, Name (..))
import LambdaProlog.Prelude (Builtins (..), prelude, tyO)

data Solution = Solution
  { solBinds :: IntMap Term
  }
  deriving stock (Eq, Show)

data Env s = Env
  { envTrail :: Trail s
  , envProg :: STRef s Program
  , envFail :: STRef s (ST s ())
  , envCut :: STRef s (ST s ())
  , envEigenN :: STRef s Int
  }

query :: Program -> [MetaId] -> Goal -> [Solution]
query = queryN maxBound

queryWithInterner :: Interner -> Program -> [MetaId] -> Goal -> [Solution]
queryWithInterner intern0 = queryNWithInterner maxBound intern0

queryN :: Int -> Program -> [MetaId] -> Goal -> [Solution]
queryN maxN = queryNWithInterner maxN (bInterner prelude)

queryNWithInterner :: Int -> Interner -> Program -> [MetaId] -> Goal -> [Solution]
queryNWithInterner maxN _intern0 prog qvars g =
  runTrail $ \tr -> do
    mapM_ (\m -> allocMeta tr m (Level 0) Nothing) qvars
    acc <- newSTRef ([] :: [Solution])
    nref <- newSTRef (0 :: Int)
    progR <- newSTRef prog
    done <- pure (pure () :: ST s ())
    failR <- newSTRef done
    cutR <- newSTRef done
    eigenN <- newSTRef (0 :: Int)
    let env = Env tr progR failR cutR eigenN
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
  ts' <- mapM (derefNf (envTrail env)) ts
  let b = prelude
  if p == bCut b && null ts'
    then solve env GCut sc
    else case interpConnective p ts' of
      Just g -> solve env g sc
      Nothing ->
        case builtinAtom p ts' of
          Just True -> sc
          Just False -> invokeFail env
          Nothing -> solveAtomClauses env p ts sc

-- | Reinterpret a constant applied to arguments as a logical connective.
-- This is what makes higher-order goal arguments work: @once (true, true)@
-- instantiates a meta to the term @',' true true@, which must be solved as
-- a conjunction, not looked up as a user predicate named @,@.
interpConnective :: Name -> [Term] -> Maybe Goal
interpConnective p ts =
  let b = prelude
   in if p == bTrue b && null ts
        then Just GTrue
        else
          if p == bFail b && null ts
            then Just GFail
            else
              if p == bCut b && null ts
                then Just GCut
                else
                  if p == bAnd b
                    then case ts of
                      [a, c] -> Just (GAnd (goalOfTerm a) (goalOfTerm c))
                      _ -> Nothing
                    else
                      if p == bOr b
                        then case ts of
                          [a, c] -> Just (GOr (goalOfTerm a) (goalOfTerm c))
                          _ -> Nothing
                        else
                          if p == bImpl b
                            then case ts of
                              [d, g] -> Just (GImpl (clausesOfTerm d) (goalOfTerm g))
                              _ -> Nothing
                            else
                              if p == bEq b
                                then case ts of
                                  [a, c] -> Just (GEq a c)
                                  _ -> Nothing
                                else
                                  if p == bIs b
                                    then case ts of
                                      [a, c] -> Just (GIs a c)
                                      _ -> Nothing
                                    else
                                      if p == bNot b
                                        then case ts of
                                          [g] -> Just (GNot (goalOfTerm g))
                                          _ -> Nothing
                                        else
                                          if p == bPi b
                                            then case ts of
                                              [f] -> Just (piGoal f)
                                              _ -> Nothing
                                            else
                                              if p == bSigma b
                                                then case ts of
                                                  [f] -> Just (sigmaGoal f)
                                                  _ -> Nothing
                                                else Nothing

-- | Read a kernel term as a goal. Used when a connective’s argument is itself
-- a compound formula (a term, not already a 'Goal').
goalOfTerm :: Term -> Goal
goalOfTerm (TLam _) = GFail
goalOfTerm (TApp h ts) = case h of
  HConst p -> case interpConnective p ts of
    Just g -> g
    Nothing -> GAtom p ts
  HMeta m -> GFlex m ts
  HBound _ -> GFail
  HLit _ -> GFail

-- | @pi@ (and n-ary @pi x y\\ …@) over a functional term.
piGoal :: Term -> Goal
piGoal f =
  GForall tyO $ \e ->
    case applySpine f [e] of
      t@(TLam _) -> piGoal t
      t -> goalOfTerm t

sigmaGoal :: Term -> Goal
sigmaGoal f =
  GExists tyO $ \e ->
    case applySpine f [e] of
      t@(TLam _) -> sigmaGoal t
      t -> goalOfTerm t

-- | Left-hand side of @=>@: a clause, or a comma-separated list of clauses.
clausesOfTerm :: Term -> [Clause]
clausesOfTerm t = case t of
  TApp (HConst p) [a, b]
    | p == bAnd prelude -> clausesOfTerm a ++ clausesOfTerm b
    | p == bDCut prelude -> [clauseHead a (goalOfTerm b)]
  _ -> [clauseHead t GTrue]

clauseHead :: Term -> Goal -> Clause
clauseHead (TApp (HConst p) args) body = Clause p [] args body
clauseHead _ _ = Clause (bFail prelude) [] [] GFail

-- | @Just True@/@Just False@ means the atom is a builtin that succeeded or
-- failed. @Nothing@ means it is an ordinary predicate.
builtinAtom :: Name -> [Term] -> Maybe Bool
builtinAtom p ts =
  let b = prelude
   in if p == bTrue b && null ts
        then Just True
        else
          if p == bFail b && null ts
            then Just False
            else
              if p == bCut b && null ts
                then Nothing -- cut must go through GCut to adjust the fail register
                else
                  if p == bLt b || p == bGt b || p == bLe b || p == bGe b
                    then case ts of
                      [a, c] -> evalCmp p a c
                      _ -> Just False
                    else Nothing

solveAtomClauses :: Env s -> Name -> [Term] -> ST s () -> ST s ()
solveAtomClauses env p ts sc = do
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
  solve env (k (TApp (HConst e) [])) $ do
    popLevel tr
    sc

internEigen :: Env s -> ST s Name
internEigen env = do
  n <- readSTRef (envEigenN env)
  writeSTRef (envEigenN env) (n + 1)
  pure (Name (1000000 + n))

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
  case evalGround rhs' of
    Nothing -> invokeFail env
    Just (GInt n) -> solveUnify env lhs (intLit n) sc
    Just (GString s) -> solveUnify env lhs (stringLit s) sc

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
    TApp (HMeta m') ts' ->
      if m' == m
        then invokeFail env
        else solveFlex env m' ts' sc
    TApp (HBound _) _ -> invokeFail env
    TApp (HLit _) _ -> invokeFail env
    TLam _ -> invokeFail env

freeze :: Trail s -> [MetaId] -> ST s Solution
freeze tr qvars = do
  pairs <- mapM (\mid -> (metaInt mid,) <$> derefNf tr (meta mid)) qvars
  pure (Solution (IntMap.fromList pairs))
