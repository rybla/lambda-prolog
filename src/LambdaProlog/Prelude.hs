-- | Pervasive kinds, constants, and interned names shared by the kernel,
-- elaborator, and pretty-printer.
module LambdaProlog.Prelude
  ( Builtins (..)
  , prelude
  , tyO
  , tyInt
  , tyString
  , tyList
  ) where

import Data.Text (Text)

import LambdaProlog.Kernel.Type (Type (..))
import LambdaProlog.Name (Interner, Name, emptyInterner, internMany)

data Builtins = Builtins
  { bInterner :: Interner
  , -- kinds / type constructors
    bO :: Name
  , bInt :: Name
  , bString :: Name
  , bList :: Name
  , -- logic
    bTrue :: Name
  , bFail :: Name
  , bCut :: Name
  , bAnd :: Name
  , bOr :: Name
  , bImpl :: Name
  , bDCut :: Name
  , bPi :: Name
  , bSigma :: Name
  , bEq :: Name
  , -- lists
    bNil :: Name
  , bCons :: Name
  , -- arith / strings
    bIs :: Name
  , bPlus :: Name
  , bMinus :: Name
  , bTimes :: Name
  , bDiv :: Name
  , bMod :: Name
  , bLt :: Name
  , bGt :: Name
  , bLe :: Name
  , bGe :: Name
  , bUMinus :: Name
  , bConcat :: Name
  , bNot :: Name
  }

preludeNames :: [Text]
preludeNames =
  [ "o"
  , "int"
  , "string"
  , "list"
  , "true"
  , "fail"
  , "!"
  , ","
  , ";"
  , "=>"
  , ":-"
  , "pi"
  , "sigma"
  , "="
  , "nil"
  , "::"
  , "is"
  , "+"
  , "-"
  , "*"
  , "div"
  , "mod"
  , "<"
  , ">"
  , "=<"
  , ">="
  , "~"
  , "^"
  , "not"
  ]

prelude :: Builtins
prelude =
  let (ns, intern) = internMany preludeNames emptyInterner
      at i = ns !! i
   in Builtins
        { bInterner = intern
        , bO = at 0
        , bInt = at 1
        , bString = at 2
        , bList = at 3
        , bTrue = at 4
        , bFail = at 5
        , bCut = at 6
        , bAnd = at 7
        , bOr = at 8
        , bImpl = at 9
        , bDCut = at 10
        , bPi = at 11
        , bSigma = at 12
        , bEq = at 13
        , bNil = at 14
        , bCons = at 15
        , bIs = at 16
        , bPlus = at 17
        , bMinus = at 18
        , bTimes = at 19
        , bDiv = at 20
        , bMod = at 21
        , bLt = at 22
        , bGt = at 23
        , bLe = at 24
        , bGe = at 25
        , bUMinus = at 26
        , bConcat = at 27
        , bNot = at 28
        }

tyO :: Type
tyO = TyCon (bO prelude) []

tyInt :: Type
tyInt = TyCon (bInt prelude) []

tyString :: Type
tyString = TyCon (bString prelude) []

tyList :: Type -> Type
tyList a = TyCon (bList prelude) [a]
