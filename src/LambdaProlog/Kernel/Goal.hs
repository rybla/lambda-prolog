-- | Abstract syntax of goals and definite clauses for uniform proof search.
module LambdaProlog.Kernel.Goal
  ( Atom (..)
  , Goal (..)
  , Clause (..)
  , Program (..)
  , emptyProgram
  , consultClause
  , consultClauses
  , addHyp
  , addHyps
  , lookupClauses
  , copyClause
  , clNVars
  , mkClause
  , mapGoal
  , mapClauseMetas
  ) where

import Control.Monad.ST (ST)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import LambdaProlog.Kernel.Term
  ( Head (..)
  , MetaId (..)
  , Term (..)
  )
import LambdaProlog.Kernel.Trail (Trail, freshMeta)
import LambdaProlog.Kernel.Type (Type)
import LambdaProlog.Name (Name)

data Atom = Atom
  { atomPred :: Name
  , atomArgs :: [Term]
  }
  deriving stock (Eq, Show)

data Goal
  = GTrue
  | GFail
  | GCut
  | GAtom Name [Term]
  | GFlex MetaId [Term]
  | GAnd Goal Goal
  | GOr Goal Goal
  | GExists Type (Term -> Goal)
  | GForall Type (Term -> Goal)
  | GImpl [Clause] Goal
  | GEq Term Term
  | GIs Term Term
  | GNot Goal

-- | A definite clause. Template variables are 'HMeta' with ids
-- listed in 'clVars'. 'copyClause' replaces those with fresh trail metas;
-- other metas are left alone (live variables from enclosing scopes).
data Clause = Clause
  { clPred :: Name
  , clVars :: [MetaId]
  , clArgs :: [Term]
  , clBody :: Goal
  }

clNVars :: Clause -> Int
clNVars = length . clVars

mkClause :: Name -> Int -> [Term] -> Goal -> Clause
mkClause p n args body = Clause p (map MetaId [0 .. n - 1]) args body

newtype Program = Program
  { progMap :: Map Name [Clause]
  }

emptyProgram :: Program
emptyProgram = Program Map.empty

-- | Add a source-order program clause (tried after existing ones).
consultClause :: Clause -> Program -> Program
consultClause c (Program m) =
  Program (Map.insertWith (\new old -> old ++ new) (clPred c) [c] m)

consultClauses :: [Clause] -> Program -> Program
consultClauses cs p = foldl (flip consultClause) p cs

-- | Hypothetical clause: tried before existing ones for that predicate.
addHyp :: Clause -> Program -> Program
addHyp c (Program m) =
  Program (Map.insertWith (++) (clPred c) [c] m)

addHyps :: [Clause] -> Program -> Program
addHyps cs p = foldl (flip addHyp) p (reverse cs)

lookupClauses :: Name -> Program -> [Clause]
lookupClauses p (Program m) = Map.findWithDefault [] p m

-- | Freshen template metas in 'clVars'.
copyClause :: Trail s -> Clause -> ST s Clause
copyClause tr c
  | null (clVars c) = pure c
  | otherwise = do
      ms <- mapM (\_ -> freshMeta tr Nothing) (clVars c)
      let m = Map.fromList (zip (clVars c) ms)
      pure
        c
          { clVars = []
          , clArgs = map (substMetas m) (clArgs c)
          , clBody = substGoalMetas m (clBody c)
          }

substMetas :: Map MetaId MetaId -> Term -> Term
substMetas m = go
  where
    go (TLam t) = TLam (go t)
    go (TApp h ts) =
      let ts' = map go ts
       in case h of
            HMeta mid ->
              case Map.lookup mid m of
                Just mid' -> TApp (HMeta mid') ts'
                Nothing -> TApp h ts'
            _ -> TApp h ts'

substGoalMetas :: Map MetaId MetaId -> Goal -> Goal
substGoalMetas m = go
  where
    s = substMetas m
    go g = case g of
      GTrue -> GTrue
      GFail -> GFail
      GCut -> GCut
      GAtom p ts -> GAtom p (map s ts)
      GFlex mid ts ->
        case Map.lookup mid m of
          Just mid' -> GFlex mid' (map s ts)
          Nothing -> GFlex mid (map s ts)
      GAnd a b -> GAnd (go a) (go b)
      GOr a b -> GOr (go a) (go b)
      GExists ty k -> GExists ty (go . k)
      GForall ty k -> GForall ty (go . k)
      GImpl cs b -> GImpl (map (mapClauseMetas m) cs) (go b)
      GEq a b -> GEq (s a) (s b)
      GIs a b -> GIs (s a) (s b)
      GNot b -> GNot (go b)

mapClauseMetas :: Map MetaId MetaId -> Clause -> Clause
mapClauseMetas m c =
  c
    { clArgs = map (substMetas m) (clArgs c)
    , clBody = substGoalMetas m (clBody c)
    }

mapGoal :: (Term -> Term) -> Goal -> Goal
mapGoal f = go
  where
    go g = case g of
      GTrue -> GTrue
      GFail -> GFail
      GCut -> GCut
      GAtom p ts -> GAtom p (map f ts)
      GFlex m ts -> GFlex m (map f ts)
      GAnd a b -> GAnd (go a) (go b)
      GOr a b -> GOr (go a) (go b)
      GExists ty k -> GExists ty (go . k)
      GForall ty k -> GForall ty (go . k)
      GImpl cs b -> GImpl (map (mapClauseTerms f) cs) (go b)
      GEq a b -> GEq (f a) (f b)
      GIs a b -> GIs (f a) (f b)
      GNot b -> GNot (go b)

mapClauseTerms :: (Term -> Term) -> Clause -> Clause
mapClauseTerms f c =
  c {clArgs = map f (clArgs c), clBody = mapGoal f (clBody c)}
