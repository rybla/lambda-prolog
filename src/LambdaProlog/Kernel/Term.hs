-- | Kernel terms: β-normal spines with de Bruijn binders, interned constants,
-- unification variables, and literals.
--
-- Invariant: the head of a 'TApp' is never a λ-abstraction. Applying a λ to
-- arguments is always done with 'applySpine', which β-reduces.
module LambdaProlog.Kernel.Term
  ( Level (..)
  , MetaId (..)
  , Lit (..)
  , Head (..)
  , Term (..)
  , var
  , con
  , meta
  , lit
  , intLit
  , stringLit
  , lam
  , lams
  , unLams
  , app
  , apps
  , applySpine
  , shift
  , instantiate
  , substBound
  , termHead
  , termArgs
  , isRigid
  , isFlex
  , mapTerm
  , foldTerm
  , occursMeta
  , occursConst
  ) where

import Data.Text (Text)

import LambdaProlog.Name (Name)

-- | Eigenvariable context depth. A meta created at level @ℓ@ may not be
-- instantiated to a term that mentions eigenconstants of level @> ℓ@.
newtype Level = Level {levelInt :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Num)

newtype MetaId = MetaId {metaInt :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord)

data Lit
  = LInt Integer
  | LString Text
  deriving stock (Eq, Ord, Show)

data Head
  = HConst Name
  | HBound Int
  | HMeta MetaId
  | HLit Lit
  deriving stock (Eq, Ord, Show)

data Term
  = TApp Head [Term]
  | TLam Term
  deriving stock (Eq, Ord, Show)

var :: Int -> Term
var i = TApp (HBound i) []

con :: Name -> Term
con n = TApp (HConst n) []

meta :: MetaId -> Term
meta m = TApp (HMeta m) []

lit :: Lit -> Term
lit l = TApp (HLit l) []

intLit :: Integer -> Term
intLit n = lit (LInt n)

stringLit :: Text -> Term
stringLit s = lit (LString s)

lam :: Term -> Term
lam = TLam

lams :: Int -> Term -> Term
lams n t = iterate TLam t !! n

unLams :: Term -> (Int, Term)
unLams = go 0
  where
    go n (TLam t) = go (n + 1) t
    go n t = (n, t)

-- | Apply a term to a single argument, β-reducing if the term is a λ.
app :: Term -> Term -> Term
app t u = applySpine t [u]

apps :: Term -> [Term] -> Term
apps = applySpine

-- | Apply a spine, peeling λs with β-reduction.
applySpine :: Term -> [Term] -> Term
applySpine t [] = t
applySpine (TLam body) (u : us) = applySpine (instantiate u body) us
applySpine (TApp h ts) us = TApp h (ts ++ us)

-- | @shift n k t@ adds @n@ to every bound index @>= k@.
shift :: Int -> Int -> Term -> Term
shift n k (TLam t) = TLam (shift n (k + 1) t)
shift n k (TApp h ts) = TApp (shiftHead n k h) (map (shift n k) ts)

shiftHead :: Int -> Int -> Head -> Head
shiftHead n k (HBound i)
  | i >= k = HBound (i + n)
  | otherwise = HBound i
shiftHead _ _ h = h

-- | Substitute @u@ for bound index 0 in the body of a λ.
instantiate :: Term -> Term -> Term
instantiate u = substBound 0 u

-- | Replace bound index @k@ with @u@ (shifted), decrementing larger indices.
substBound :: Int -> Term -> Term -> Term
substBound k u (TLam t) = TLam (substBound (k + 1) u t)
substBound k u (TApp h ts) =
  let ts' = map (substBound k u) ts
   in case h of
        HBound i
          | i == k -> applySpine (shift k 0 u) ts'
          | i > k -> TApp (HBound (i - 1)) ts'
          | otherwise -> TApp h ts'
        _ -> TApp h ts'

termHead :: Term -> Maybe Head
termHead (TApp h _) = Just h
termHead TLam {} = Nothing

termArgs :: Term -> [Term]
termArgs (TApp _ ts) = ts
termArgs TLam {} = []

isRigid :: Term -> Bool
isRigid (TApp HMeta {} _) = False
isRigid (TApp _ _) = True
isRigid TLam {} = True

isFlex :: Term -> Bool
isFlex (TApp HMeta {} _) = True
isFlex _ = False

mapTerm :: (Term -> Term) -> Term -> Term
mapTerm f = go
  where
    go t = f $ case t of
      TLam b -> TLam (go b)
      TApp h ts -> TApp h (map go ts)

foldTerm :: (Term -> r -> r) -> r -> Term -> r
foldTerm f z t = f t $ case t of
  TLam b -> foldTerm f z b
  TApp _ ts -> foldr (flip (foldTerm f)) z ts

occursMeta :: MetaId -> Term -> Bool
occursMeta m = go
  where
    go (TLam b) = go b
    go (TApp h ts) =
      case h of
        HMeta m' | m == m' -> True
        _ -> any go ts

occursConst :: Name -> Term -> Bool
occursConst n = go
  where
    go (TLam b) = go b
    go (TApp h ts) =
      case h of
        HConst n' | n == n' -> True
        _ -> any go ts
