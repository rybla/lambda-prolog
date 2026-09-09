-- | Evaluable arithmetic and comparison for the @is@ builtin.
module LambdaProlog.Kernel.Builtin
  ( evalArith
  , cmpInt
  ) where

import LambdaProlog.Kernel.Term (Head (..), Lit (..), Term (..))
import LambdaProlog.Name (Name)
import LambdaProlog.Prelude (Builtins (..), prelude)

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
