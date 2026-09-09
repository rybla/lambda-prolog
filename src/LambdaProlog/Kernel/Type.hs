-- | Simple types and prenex type schemes. Type constructors are interned
-- 'Name's (including the pervasives @o@, @int@, @string@, and @list@).
module LambdaProlog.Kernel.Type
  ( Type (..)
  , Scheme (..)
  , tyArrs
  , tyArgs
  , tyResult
  , tyArity
  , mapType
  , typeOccurs
  , substTyGen
  ) where

import LambdaProlog.Name (Name)

-- | Monotypes. @TyGen i@ is a generic variable bound by an enclosing 'Scheme'
-- (de Bruijn, 0 = innermost). @TyMeta i@ is a unification variable used only
-- during type inference.
data Type
  = TyCon Name [Type]
  | TyArr Type Type
  | TyGen Int
  | TyMeta Int
  deriving stock (Eq, Ord, Show)

-- | @Scheme n t@ means @∀α₀…αₙ₋₁. t@ with @TyGen@ indices referring to those
-- binders.
data Scheme = Scheme
  { schemeArity :: Int
  , schemeBody :: Type
  }
  deriving stock (Eq, Ord, Show)

-- | @tyArrs [a,b] c@ is @a -> b -> c@.
tyArrs :: [Type] -> Type -> Type
tyArrs args res = foldr TyArr res args

-- | Peel a chain of arrows: @a -> b -> c@ becomes @([a,b], c)@.
tyArgs :: Type -> ([Type], Type)
tyArgs (TyArr a b) =
  let (as, r) = tyArgs b
   in (a : as, r)
tyArgs t = ([], t)

tyResult :: Type -> Type
tyResult t = snd (tyArgs t)

tyArity :: Type -> Int
tyArity t = length (fst (tyArgs t))

mapType :: (Type -> Type) -> Type -> Type
mapType f t = f (go t)
  where
    go (TyCon n ts) = TyCon n (map go ts)
    go (TyArr a b) = TyArr (go a) (go b)
    go x@TyGen {} = x
    go x@TyMeta {} = x

typeOccurs :: (Type -> Bool) -> Type -> Bool
typeOccurs p t
  | p t = True
  | otherwise =
      case t of
        TyCon _ ts -> any (typeOccurs p) ts
        TyArr a b -> typeOccurs p a || typeOccurs p b
        TyGen _ -> False
        TyMeta _ -> False

-- | Instantiate a prenex body: @TyGen i@ becomes @ts !! i@. Schemes are
-- prenex, so there is no shifting of leftover binders.
substTyGen :: [Type] -> Type -> Type
substTyGen ts = go
  where
    go (TyGen i)
      | i >= 0 && i < length ts = ts !! i
      | otherwise = TyGen i
    go (TyCon c args) = TyCon c (map go args)
    go (TyArr a b) = TyArr (go a) (go b)
    go m@TyMeta {} = m
