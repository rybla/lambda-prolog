-- | Evaluable arithmetic, strings, and comparison for builtins.
module LambdaProlog.Kernel.Builtin
  ( Ground (..)
  , evalArith
  , evalString
  , evalGround
  , cmpInt
  , evalCmp
  , lcgStep
  , lcgVal
  ) where

import Data.Bits ((.&.), shiftR)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Read qualified as TR

import LambdaProlog.Kernel.Term (Head (..), Lit (..), Term (..))
import LambdaProlog.Name (Name)
import LambdaProlog.Prelude (Builtins (..), prelude)

data Ground
  = GInt Integer
  | GString Text
  deriving stock (Eq, Show)

-- | 64-bit LCG step (Knuth / MMIX parameters):
-- multiplier = 6364136223846793005, addend = 1442695040888963407
lcgStep :: Integer -> Integer
lcgStep s =
  let mask64 = 0xFFFFFFFFFFFFFFFF
      s' = (s * 6364136223846793005 + 1442695040888963407) .&. mask64
   in s'

-- | Extract a non-negative 31-bit random integer from the upper bits of the seed.
lcgVal :: Integer -> Integer
lcgVal s =
  let s' = lcgStep s
   in (s' `shiftR` 32) .&. 0x7FFFFFFF

-- | Evaluate a ground arithmetic expression to an integer.
evalArith :: Term -> Maybe Integer
evalArith (TApp (HLit (LInt n)) []) = Just n
evalArith (TApp (HConst c) args) =
  let b = prelude
   in case args of
        [x]
          | c == bUMinus b -> negate <$> evalArith x
          | c == bPrngNextSeed b -> lcgStep <$> evalArith x
          | c == bPrngNextVal b -> lcgVal <$> evalArith x
          | c == bStrLen b -> fromIntegral . T.length <$> evalString x
          | c == bParseInt b -> do
              txt <- evalString x
              case TR.signed TR.decimal (T.strip txt) of
                Right (n, rest) | T.null rest -> Just n
                _ -> Nothing
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
        [s, low, high]
          | c == bPrngRangeVal b -> do
              s0 <- evalArith s
              l <- evalArith low
              h <- evalArith high
              if h < l
                then Nothing
                else
                  let spanLen = h - l + 1
                      v = l + (lcgVal s0 `rem` spanLen)
                   in Just v
        _ -> Nothing
evalArith _ = Nothing

evalString :: Term -> Maybe Text
evalString (TApp (HLit (LString s)) []) = Just s
evalString (TApp (HConst c) [x])
  | c == bToString prelude = case evalGround x of
      Just (GInt n) -> Just (T.pack (show n))
      Just (GString s) -> Just s
      Nothing -> Nothing
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

