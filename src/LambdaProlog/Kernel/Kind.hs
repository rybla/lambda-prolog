-- | Kinds of type constructors. @type@ is the kind of types; @type -> type@
-- is the kind of unary constructors such as @list@.
module LambdaProlog.Kernel.Kind
  ( Kind (..)
  , kindArity
  ) where

-- | @KType@ prints as @type@. @KArr k1 k2@ is a type constructor kind.
data Kind
  = KType
  | KArr Kind Kind
  deriving stock (Eq, Ord, Show)

-- | Number of type arguments a constructor of this kind expects.
kindArity :: Kind -> Int
kindArity KType = 0
kindArity (KArr _ k) = 1 + kindArity k
