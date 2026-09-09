-- | De Bruijn shifting, instantiation, and β-normalization. Meta cells are
-- not dereferenced here; unification supplies a deref-aware normalizer.
--
-- 'shift', 'instantiate', and 'substBound' are defined next to the term
-- constructors (so 'applySpine' can β-reduce without a cyclic import) and
-- re-exported from here.
module LambdaProlog.Kernel.Subst
  ( shift
  , instantiate
  , substBound
  , betaNf
  , etaExpand
  , closeTerm
  ) where

import LambdaProlog.Kernel.Term
  ( Term (..)
  , applySpine
  , instantiate
  , lams
  , shift
  , substBound
  , var
  )

-- | Recursively normalize arguments. Spines are already β-normal when built
-- with 'applySpine'; this walks under λs and inside arguments.
betaNf :: Term -> Term
betaNf (TLam t) = TLam (betaNf t)
betaNf (TApp h ts) = TApp h (map betaNf ts)

-- | η-expand a term to have at least @n@ outer lambdas:
-- @η_n(t) = λ…λ. t xₙ₋₁ … x₀@.
etaExpand :: Int -> Term -> Term
etaExpand n t
  | n <= 0 = t
  | otherwise =
      let t' = shift n 0 t
          args = map var (reverse [0 .. n - 1])
       in lams n (applySpine t' args)

-- | Wrap a term in @n@ lambdas. Dual of peeling binders with 'unLams'.
closeTerm :: Int -> Term -> Term
closeTerm = lams
