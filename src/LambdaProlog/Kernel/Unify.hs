-- | Higher-order pattern unification (Miller / Nipkow). Flexible terms must
-- be metas applied to distinct bound variables or eigenconstants. Anything
-- outside that fragment is 'NotPattern'.
module LambdaProlog.Kernel.Unify
  ( UnifyError (..)
  , unify
  , unifyPure
  , whnf
  , derefNf
  ) where

import Control.Monad (filterM)
import Control.Monad.ST (ST)
import Data.IntMap.Strict (IntMap)
import Data.List (findIndex)

import LambdaProlog.Kernel.Term
  ( Head (..)
  , Level (..)
  , MetaId (..)
  , Term (..)
  , applySpine
  , lams
  , shift
  , var
  )
import LambdaProlog.Kernel.Trail
  ( Trail
  , bindMeta
  , eigenLevel
  , freshMeta
  , freshMetaAt
  , mark
  , mcBind
  , mcLevel
  , readMeta
  , runTrail
  , snapshotBinds
  , unwind
  )
import LambdaProlog.Name (Name)

data UnifyError
  = Clash Head Head
  | Occurs MetaId
  | NotPattern Term
  | Scope MetaId
  | ArityMismatch
  deriving stock (Eq, Show)

-- | Atomic unification: on failure the trail is restored to its state at
-- the call.
unify :: Trail s -> Term -> Term -> ST s (Either UnifyError ())
unify tr s t = do
  m <- mark tr
  r <- unifyD tr 0 s t
  case r of
    Left e -> unwind tr m >> pure (Left e)
    Right () -> pure (Right ())

-- | Pure wrapper used by tests. Metas mentioned in the terms are allocated
-- at level 0.
unifyPure :: Term -> Term -> Either UnifyError (IntMap Term)
unifyPure s t =
  runTrail $ \tr -> do
    r <- unify tr s t
    case r of
      Left e -> pure (Left e)
      Right () -> Right <$> snapshotBinds tr

unifyD :: Trail s -> Int -> Term -> Term -> ST s (Either UnifyError ())
unifyD tr d s t = do
  s' <- whnf tr s
  t' <- whnf tr t
  case (s', t') of
    (TLam sB, TLam tB) -> unifyD tr (d + 1) sB tB
    (TLam sB, _) ->
      unifyD tr (d + 1) sB (applySpine (shift 1 0 t') [var 0])
    (_, TLam tB) ->
      unifyD tr (d + 1) (applySpine (shift 1 0 s') [var 0]) tB
    (TApp h1 a1, TApp h2 a2) -> unifyApp tr d h1 a1 h2 a2

unifyApp ::
  Trail s ->
  Int ->
  Head ->
  [Term] ->
  Head ->
  [Term] ->
  ST s (Either UnifyError ())
unifyApp tr d h1 a1 h2 a2 =
  case (h1, h2) of
    (HMeta m1, HMeta m2) -> flexFlex tr d m1 a1 m2 a2
    (HMeta m1, _) -> flexRigid tr d m1 a1 (TApp h2 a2)
    (_, HMeta m2) -> flexRigid tr d m2 a2 (TApp h1 a1)
    _
      | h1 == h2 ->
          if length a1 /= length a2
            then pure (Left ArityMismatch)
            else unifyList tr d a1 a2
      | otherwise -> pure (Left (Clash h1 h2))

unifyList :: Trail s -> Int -> [Term] -> [Term] -> ST s (Either UnifyError ())
unifyList _ _ [] [] = pure (Right ())
unifyList tr d (x : xs) (y : ys) = do
  r <- unifyD tr d x y
  case r of
    Left e -> pure (Left e)
    Right () -> unifyList tr d xs ys
unifyList _ _ _ _ = pure (Left ArityMismatch)

-- | Weak head: follow a bound meta at the spine head and β-reduce.
whnf :: Trail s -> Term -> ST s Term
whnf _tr (TLam t) = pure (TLam t)
whnf tr t@(TApp (HMeta m) args) = do
  cell <- readMeta tr m
  case mcBind cell of
    Nothing -> pure t
    Just v -> whnf tr (applySpine v args)
whnf _ t = pure t

-- | Full β-normal form with metas dereferenced.
derefNf :: Trail s -> Term -> ST s Term
derefNf tr t = do
  t' <- whnf tr t
  case t' of
    TLam b -> TLam <$> derefNf tr b
    TApp h args -> TApp h <$> mapM (derefNf tr) args

data Pat
  = PatBound Int
  | PatEigen Name
  deriving stock (Eq, Show)

patternArgs :: Trail s -> [Term] -> ST s (Either UnifyError [Pat])
patternArgs tr args = do
  ps <- mapM (patArg tr) args
  case sequence ps of
    Left e -> pure (Left e)
    Right pats ->
      if unique pats
        then pure (Right pats)
        else pure (Left (NotPattern (TApp (HBound 0) args)))
  where
    unique xs = xs == nubEq xs
    nubEq [] = []
    nubEq (x : xs) = x : nubEq (filter (/= x) xs)

patArg :: Trail s -> Term -> ST s (Either UnifyError Pat)
patArg tr t = do
  t' <- whnf tr t
  case t' of
    TApp (HBound i) [] -> pure (Right (PatBound i))
    TApp (HConst n) [] -> do
      ml <- eigenLevel tr n
      case ml of
        Just _ -> pure (Right (PatEigen n))
        Nothing -> pure (Left (NotPattern t'))
    _ -> pure (Left (NotPattern t'))

flexRigid ::
  Trail s ->
  Int ->
  MetaId ->
  [Term] ->
  Term ->
  ST s (Either UnifyError ())
flexRigid tr _d m args t = do
  tNf <- derefNf tr t
  if occursMetaDeep m tNf
    then pure (Left (Occurs m))
    else do
      ps <- patternArgs tr args
      case ps of
        Left e -> pure (Left e)
        Right pats -> do
          cell <- readMeta tr m
          inv <- invert tr 0 (mcLevel cell) m pats tNf
          case inv of
            Left e -> pure (Left e)
            Right body -> do
              bindMeta tr m (lams (length pats) body)
              pure (Right ())

occursMetaDeep :: MetaId -> Term -> Bool
occursMetaDeep m = go
  where
    go (TLam b) = go b
    go (TApp h ts) =
      case h of
        HMeta m' | m == m' -> True
        _ -> any go ts

-- | Build the *body* (no λ-prefix) of the instantiation of @m@, walking @t@
-- at λ-depth @d@ (plus extra under @t@'s own binders). Bound variables not
-- in the pattern are a scope error; younger eigenconstants not in the
-- pattern are a scope error; other metas are pruned to the allowed set.
invert ::
  Trail s ->
  Int ->
  Level ->
  MetaId ->
  [Pat] ->
  Term ->
  ST s (Either UnifyError Term)
invert tr extra0 mLev m pats = go extra0
  where
    k = length pats

    go extra (TLam b) = do
      r <- go (extra + 1) b
      pure (TLam <$> r)
    go extra (TApp h as) =
      case h of
        HMeta m'
          | m' == m -> pure (Left (Occurs m))
          | otherwise -> prune tr extra m mLev pats m' as
        _ -> do
          asR <- mapM (go extra) as
          case sequence asR of
            Left e -> pure (Left e)
            Right as' ->
              case h of
                HBound i
                  | i < extra -> pure (Right (TApp (HBound i) as'))
                  | otherwise ->
                      let outer = i - extra
                       in case findIndex (== PatBound outer) pats of
                            Just p ->
                              let new = extra + (k - 1 - p)
                               in pure (Right (TApp (HBound new) as'))
                            Nothing -> pure (Left (Scope m))
                HConst n -> do
                  ml <- eigenLevel tr n
                  case ml of
                    Just lev ->
                      case findIndex (== PatEigen n) pats of
                        Just p ->
                          let new = extra + (k - 1 - p)
                           in pure (Right (TApp (HBound new) as'))
                        Nothing
                          | lev <= mLev -> pure (Right (TApp (HConst n) as'))
                          | otherwise -> pure (Left (Scope m))
                    Nothing -> pure (Right (TApp (HConst n) as'))
                HLit l -> pure (Right (TApp (HLit l) as'))

-- | Restrict a foreign meta so it only depends on pattern variables that
-- @m@ is allowed to mention.
prune ::
  Trail s ->
  Int ->
  MetaId ->
  Level ->
  [Pat] ->
  MetaId ->
  [Term] ->
  ST s (Either UnifyError Term)
prune tr extra m mLev pats z args = do
  zCell <- readMeta tr z
  case mcBind zCell of
    Just v -> invert tr extra mLev m pats (applySpine v args)
    Nothing -> do
      ps <- patternArgs tr args
      case ps of
        Left e -> pure (Left e)
        Right zpats -> do
          kept <- filterM (isAllowedPat tr extra mLev pats) zpats
          if length kept == length zpats
            then do
              as' <- mapM (invert tr extra mLev m pats) args
              case sequence as' of
                Left e -> pure (Left e)
                Right as'' -> pure (Right (TApp (HMeta z) as''))
            else do
              z' <- freshMetaAt tr (mcLevel zCell) Nothing
              let kZ = length zpats
                  keptIdxs = [i | (i, p) <- zip [0 ..] zpats, p `elem` kept]
                  body =
                    TApp
                      (HMeta z')
                      [var (kZ - 1 - p) | p <- keptIdxs]
              bindMeta tr z (lams kZ body)
              as' <- mapM (invert tr extra mLev m pats) [args !! i | i <- keptIdxs]
              case sequence as' of
                Left e -> pure (Left e)
                Right as'' -> pure (Right (TApp (HMeta z') as''))

isAllowedPat :: Trail s -> Int -> Level -> [Pat] -> Pat -> ST s Bool
isAllowedPat tr extra mLev pats p = case p of
  PatBound i
    | i < extra -> pure True
    | otherwise -> pure (PatBound (i - extra) `elem` pats)
  PatEigen n
    | PatEigen n `elem` pats -> pure True
    | otherwise -> do
        ml <- eigenLevel tr n
        pure $ case ml of
          Just lev -> lev <= mLev
          Nothing -> True

flexFlex ::
  Trail s ->
  Int ->
  MetaId ->
  [Term] ->
  MetaId ->
  [Term] ->
  ST s (Either UnifyError ())
flexFlex tr _d m1 a1 m2 a2
  | m1 == m2 && a1 == a2 = pure (Right ())
  | m1 == m2 = sameMeta tr m1 a1 a2
  | otherwise = diffMeta tr m1 a1 m2 a2

sameMeta ::
  Trail s ->
  MetaId ->
  [Term] ->
  [Term] ->
  ST s (Either UnifyError ())
sameMeta tr m a1 a2 = do
  p1 <- patternArgs tr a1
  p2 <- patternArgs tr a2
  case (p1, p2) of
    (Right ps1, Right ps2)
      | length ps1 == length ps2 -> do
          let k = length ps1
              kept =
                [ i
                | (i, x, y) <- zip3 [0 ..] ps1 ps2
                , x == y
                ]
          if length kept == k
            then pure (Right ())
            else do
              z <- freshMeta tr Nothing
              let body =
                    TApp
                      (HMeta z)
                      [var (k - 1 - i) | i <- kept]
              bindMeta tr m (lams k body)
              pure (Right ())
    (Left e, _) -> pure (Left e)
    (_, Left e) -> pure (Left e)
    _ -> pure (Left ArityMismatch)

diffMeta ::
  Trail s ->
  MetaId ->
  [Term] ->
  MetaId ->
  [Term] ->
  ST s (Either UnifyError ())
diffMeta tr m1 a1 m2 a2 = do
  p1 <- patternArgs tr a1
  p2 <- patternArgs tr a2
  case (p1, p2) of
    (Right ps1, Right ps2) -> do
      c1 <- readMeta tr m1
      c2 <- readMeta tr m2
      z <- freshMetaAt tr (min (mcLevel c1) (mcLevel c2)) Nothing
      let common = [p | p <- ps1, p `elem` ps2]
          inst ps =
            let k = length ps
             in lams
                  k
                  ( TApp
                      (HMeta z)
                      [ case findIndex (== c) ps of
                          Just i -> var (k - 1 - i)
                          Nothing -> var 0
                      | c <- common
                      ]
                  )
      bindMeta tr m1 (inst ps1)
      bindMeta tr m2 (inst ps2)
      pure (Right ())
    (Left e, _) -> pure (Left e)
    (_, Left e) -> pure (Left e)
