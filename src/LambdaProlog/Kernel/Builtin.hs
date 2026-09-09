-- | Evaluable arithmetic, strings, and comparison for builtins.
module LambdaProlog.Kernel.Builtin
  ( Ground (..)
  , evalArith
  , evalString
  , evalGround
  , cmpInt
  , evalCmp
  ) where

import Data.Text (Text)

import LambdaProlog.Kernel.Term (Head (..), Lit (..), Term (..))
import LambdaProlog.Name (Name)
import LambdaProlog.Prelude (Builtins (..), prelude)

data Ground
  = GInt Integer
  | GString Text
  deriving stock (Eq, Show)

-- | Evaluate a ground arithmetic expression to an integer.
evalArith :: Term -> Maybe Integer
evalArith (TApp (HLit (LInt n)) []) = Just n
evalArith (TApp (HConst c) args) =
  let b = prelude
   in case args of
        [x]
          | c == bUMinus b -> negate <$> evalArith x
        [x, y]
          | c == bPlus b -> (+) <$> evalArith x <*> evalArith y
          | c == bMinus b -> (-) <$> evalArith x <*> evalArith y
          | c == bTimes b -> (*) <$> evalArith x <*> evalArith y
          | c == bDiv b -> do
              a <- evalArith x
              d <- evalArith y
              if d == 0 then Nothing else Just (a `quot` d)
          | c == bMod b -> do
              a <- evalArith x
              d <- evalArith y
              if d == 0 then Nothing else Just (a `rem` d)
        _ -> Nothing
evalArith _ = Nothing

evalString :: Term -> Maybe Text
evalString (TApp (HLit (LString s)) []) = Just s
evalString (TApp (HConst c) [x, y])
  | c == bConcat prelude = (<>) <$> evalString x <*> evalString y
evalString _ = Nothing

evalGround :: Term -> Maybe Ground
evalGround t =
  case evalArith t of
    Just n -> Just (GInt n)
    Nothing -> GString <$> evalString t

cmpInt :: Name -> Integer -> Integer -> Maybe Bool
cmpInt op a b =
  let p = prelude
   in if op == bLt p
        then Just (a < b)
        else
          if op == bGt p
            then Just (a > b)
            else
              if op == bLe p
                then Just (a <= b)
                else
                  if op == bGe p
                    then Just (a >= b)
                    else Nothing

-- | Evaluate a comparison predicate on two (already dereferenced) terms.
evalCmp :: Name -> Term -> Term -> Maybe Bool
evalCmp op a b = do
  x <- evalArith a
  y <- evalArith b
  cmpInt op x y

