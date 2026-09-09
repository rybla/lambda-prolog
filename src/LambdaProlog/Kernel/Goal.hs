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
  , mapGoal
  , mapClause
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
-- @0 .. clNVars-1@. 'copyClause' replaces those with fresh trail metas;
-- ids @>= clNVars@ are left alone (live query variables in hypotheticals).
data Clause = Clause
  { clPred :: Name
  , clNVars :: Int
  , clArgs :: [Term]
  , clBody :: Goal
  }

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

-- | Freshen template metas @0..clNVars-1@.
copyClause :: Trail s -> Clause -> ST s Clause
copyClause tr c
  | clNVars c <= 0 = pure c
  | otherwise = do
      ms <- mapM (\_ -> freshMeta tr Nothing) [0 .. clNVars c - 1]
      let subst t = substTmps (clNVars c) ms t
      pure
        c
          { clNVars = 0
          , clArgs = map subst (clArgs c)
          , clBody = substGoalTmps (clNVars c) ms (clBody c)
          }

substTmps :: Int -> [MetaId] -> Term -> Term
substTmps n ms = go
  where
    go (TLam t) = TLam (go t)
    go (TApp h ts) =
      let ts' = map go ts
       in case h of
            HMeta (MetaId i)
              | i >= 0 && i < n -> TApp (HMeta (ms !! i)) ts'
            _ -> TApp h ts'

substGoalTmps :: Int -> [MetaId] -> Goal -> Goal
substGoalTmps n ms = go
  where
    s = substTmps n ms
    go g = case g of
      GTrue -> GTrue
      GFail -> GFail
      GCut -> GCut
      GAtom p ts -> GAtom p (map s ts)
      GFlex (MetaId i) ts
        | i >= 0 && i < n -> GFlex (ms !! i) (map s ts)
        | otherwise -> GFlex (MetaId i) (map s ts)
      GAnd a b -> GAnd (go a) (go b)
      GOr a b -> GOr (go a) (go b)
      GExists ty k -> GExists ty (go . k)
      GForall ty k -> GForall ty (go . k)
      GImpl cs b -> GImpl (map (mapClause n ms) cs) (go b)
      GEq a b -> GEq (s a) (s b)
      GIs a b -> GIs (s a) (s b)
      GNot b -> GNot (go b)

mapClause :: Int -> [MetaId] -> Clause -> Clause
mapClause n ms c
  | clNVars c > 0 = c -- nested templates keep their own numbering
  | otherwise =
      c
        { clArgs = map (substTmps n ms) (clArgs c)
        , clBody = substGoalTmps n ms (clBody c)
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
