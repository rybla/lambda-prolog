-- | Semantic roles for surface syntax, used by the website highlighter.
module LambdaProlog.Surface.Annotate
  ( Role (..)
  , Mark (..)
  , marksModule
  , roleClass
  , roleTip
  ) where

import Data.Char (isUpper)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import LambdaProlog.Span (SrcSpan)
import LambdaProlog.Surface.Fixity (defaultOps)
import LambdaProlog.Surface.Syntax

data Role
  = RKeyword
  | RBinder
  | RLogicVar
  | RConst
  | ROperator
  | RPredicate
  | RTypeCon
  | RLiteral
  | RPi
  | RImpl
  | RComment
  deriving stock (Eq, Show)

data Mark = Mark
  { markSpan :: SrcSpan
  , markRole :: Role
  , markTip :: Text
  }

roleClass :: Role -> Text
roleClass r = case r of
  RKeyword -> "lp-kw"
  RBinder -> "lp-binder"
  RLogicVar -> "lp-var"
  RConst -> "lp-const"
  ROperator -> "lp-op"
  RPredicate -> "lp-pred"
  RTypeCon -> "lp-ty"
  RLiteral -> "lp-lit"
  RPi -> "lp-pi"
  RImpl -> "lp-impl"
  RComment -> "lp-comment"

roleTip :: Role -> Text -> Text
roleTip r name = case r of
  RKeyword -> "keyword " <> name
  RBinder -> "binder " <> name
  RLogicVar -> "logic variable " <> name
  RConst -> "constant " <> name
  ROperator -> "operator " <> name <> " — mixfix connective"
  RPredicate -> "predicate " <> name
  RTypeCon -> "type constructor " <> name
  RLiteral -> "literal"
  RPi -> "universal goal (pi): introduce a fresh eigenvariable"
  RImpl -> "hypothetical implication (=>): the left-hand clauses are added while proving the right-hand goal"
  RComment -> "comment"

marksModule :: Module -> [Mark]
marksModule m = concatMap marksDecl (modDecls m)

marksDecl :: Decl -> [Mark]
marksDecl d = case d of
  DKind ids _ -> map (\i -> identMark RTypeCon i) ids
  DType ids _ -> map (\i -> identMark RPredicate i) ids
  DClause t -> marksTerm t
  DLocal ids _ -> map (\i -> identMark RConst i) ids
  DFixity _ _ ids -> map (\i -> identMark ROperator i) ids
  _ -> []

marksTerm :: STerm -> [Mark]
marksTerm t = case t of
  SId i -> [identMark (idRole i) i]
  SInt s _ -> [Mark s RLiteral "integer literal"]
  SString s _ -> [Mark s RLiteral "string literal"]
  SSeq _ xs -> concatMap marksTerm xs
  SApp _ a b -> marksTerm a ++ marksTerm b
  SLam _ x _ b -> identMark RBinder x : marksTerm b
  SList _ es tl -> concatMap marksTerm es ++ maybe [] marksTerm tl
  SParen _ a -> marksTerm a
  SAnn _ a _ -> marksTerm a
  SCut s -> [Mark s RKeyword "cut (!): discard remaining alternatives of this call"]

idRole :: Ident -> Role
idRole i
  | identName i == "pi" = RPi
  | identName i == "sigma" = RPi
  | identName i == "=>" = RImpl
  | identName i `elem` ["true", "fail", "not"] = RKeyword
  | identName i `Map.member` defaultOps = ROperator
  | isVar (identName i) = RLogicVar
  | otherwise = RConst
  where
    isVar t = case T.uncons t of
      Just (c, _) -> isUpper c || c == '_'
      Nothing -> False

identMark :: Role -> Ident -> Mark
identMark r i = Mark (identLoc i) r (roleTip r (identName i))
