-- | Mixfix resolution: turn juxtaposition sequences into applications using
-- a table of infix/prefix/postfix operators.
module LambdaProlog.Surface.Fixity
  ( OpInfo (..)
  , OpTable
  , defaultOps
  , insertOp
  , mixfixTerm
  , mixfixModule
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)

import LambdaProlog.Error (Error, mkError)
import LambdaProlog.Span (combineSpans)
import LambdaProlog.Surface.Syntax

data OpInfo = OpInfo
  { opKind :: FixityKind
  , opPrec :: Int
  }
  deriving stock (Eq, Show)

type OpTable = Map Text OpInfo

-- | Teyjus-like defaults. Higher 'opPrec' binds tighter. Application is
-- treated as left-associative at precedence 1000.
defaultOps :: OpTable
defaultOps =
  Map.fromList
    [ (":-", OpInfo FxInfix 0)
    , (";", OpInfo FxInfixr 100)
    , (",", OpInfo FxInfixr 110)
    , ("=>", OpInfo FxInfixr 120)
    , ("=", OpInfo FxInfix 130)
    , ("<", OpInfo FxInfix 130)
    , (">", OpInfo FxInfix 130)
    , ("=<", OpInfo FxInfix 130)
    , (">=", OpInfo FxInfix 130)
    , ("::", OpInfo FxInfixr 140)
    , ("+", OpInfo FxInfixl 150)
    , ("-", OpInfo FxInfixl 150)
    , ("*", OpInfo FxInfixl 160)
    , ("div", OpInfo FxInfixl 160)
    , ("mod", OpInfo FxInfixl 160)
    , ("^", OpInfo FxInfixr 150)
    , ("~", OpInfo FxPrefix 180)
    , ("is", OpInfo FxInfix 130)
    ]

insertOp :: Text -> OpInfo -> OpTable -> OpTable
insertOp = Map.insert

mixfixModule :: OpTable -> Module -> Either Error Module
mixfixModule tab0 m = do
  let tab = foldl addDecl tab0 (modDecls m)
  decls <- mapM (mixfixDecl tab) (modDecls m)
  pure m {modDecls = decls}
  where
    addDecl tab d = case d of
      DFixity fx n ids ->
        foldl (\t i -> insertOp (identName i) (OpInfo fx n) t) tab ids
      _ -> tab

mixfixDecl :: OpTable -> Decl -> Either Error Decl
mixfixDecl tab d = case d of
  DClause t -> DClause <$> mixfixTerm tab t
  DQuery opts t -> DQuery opts <$> mixfixTerm tab t
  _ -> Right d

mixfixTerm :: OpTable -> STerm -> Either Error STerm
mixfixTerm tab t = case t of
  SSeq _ ts -> do
    ts' <- mapM (mixfixTerm tab) ts
    climb tab ts'
  SLam sp x ty b -> SLam sp x ty <$> mixfixTerm tab b
  SList sp es tl ->
    SList sp <$> mapM (mixfixTerm tab) es <*> traverse (mixfixTerm tab) tl
  SParen _ inner -> mixfixTerm tab inner
  SAnn sp a ty -> SAnn sp <$> mixfixTerm tab a <*> pure ty
  SApp sp a b -> SApp sp <$> mixfixTerm tab a <*> mixfixTerm tab b
  _ -> Right t

appPrec :: Int
appPrec = 1000

climb :: OpTable -> [STerm] -> Either Error STerm
climb _ [] = Left (mkError "empty term")
climb tab ts = do
  (t, rest) <- expr tab 0 ts
  case rest of
    [] -> Right t
    _ -> Left (mkError "could not resolve mixfix operators")

expr :: OpTable -> Int -> [STerm] -> Either Error (STerm, [STerm])
expr tab minP xs = do
  (left, xs1) <- prefix tab xs
  infixOps tab minP left xs1

prefix :: OpTable -> [STerm] -> Either Error (STerm, [STerm])
prefix _ [] = Left (mkError "unexpected end of term")
prefix tab (t : ts) =
  case opOf tab t of
    Just (OpInfo FxPrefix p) -> do
      (arg, rest) <- expr tab p ts
      Right (SApp (combineSpans (termSpan t) (termSpan arg)) t arg, rest)
    _ -> Right (t, ts)

infixOps :: OpTable -> Int -> STerm -> [STerm] -> Either Error (STerm, [STerm])
infixOps _ _ left [] = Right (left, [])
infixOps tab minP left (t : ts) =
  case opOf tab t of
    Just (OpInfo FxPostfix p)
      | p >= minP ->
          infixOps tab minP (SApp (combineSpans (termSpan left) (termSpan t)) t left) ts
    Just (OpInfo k p)
      | isInfix k && p >= minP -> do
          let next = if k == FxInfixr then p else p + 1
          (right, rest) <- expr tab next ts
          let sp = combineSpans (termSpan left) (termSpan right)
              -- curried: (op left) right
              e = SApp sp (SApp (combineSpans (termSpan t) (termSpan left)) t left) right
          infixOps tab minP e rest
    _
      | appPrec >= minP && not (isAnyOp tab t) ->
          let e = SApp (combineSpans (termSpan left) (termSpan t)) left t
           in infixOps tab minP e ts
    _ -> Right (left, t : ts)

isInfix :: FixityKind -> Bool
isInfix FxInfix = True
isInfix FxInfixl = True
isInfix FxInfixr = True
isInfix _ = False

opOf :: OpTable -> STerm -> Maybe OpInfo
opOf tab (SId i) = Map.lookup (identName i) tab
opOf _ _ = Nothing

isAnyOp :: OpTable -> STerm -> Bool
isAnyOp tab t = case opOf tab t of
  Just {} -> True
  Nothing -> False
