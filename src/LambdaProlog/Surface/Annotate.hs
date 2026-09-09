-- | Semantic roles for surface syntax, used by the website highlighter.
module LambdaProlog.Surface.Annotate
  ( Role (..)
  , Mark (..)
  , marksModule
  , marksSource
  , annotateSource
  , roleClass
  , roleTip
  , mergeMarks
  ) where

import Data.Char (isAlphaNum, isLower, isSpace, isUpper)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T

import LambdaProlog.Span (SrcPos (..), SrcSpan (..))
import LambdaProlog.Surface.Fixity (defaultOps, mixfixModule)
import LambdaProlog.Surface.Parser (parseModule)
import LambdaProlog.Surface.Syntax

data Role
  = RKeyword
  | RModuleName
  | RBinder
  | RLogicVar
  | RConst
  | ROperator
  | RPredicate
  | RTypeCon
  | RTyVar
  | RKindStar
  | RLiteral
  | RPi
  | RImpl
  | RPunct
  | RComment
  | RMetaKey
  | RMetaVal
  deriving stock (Eq, Ord, Show)

data Mark = Mark
  { markSpan :: SrcSpan
  , markRole :: Role
  , markTip :: Text
  }

roleClass :: Role -> Text
roleClass r = case r of
  RKeyword -> "lp-kw"
  RModuleName -> "lp-mod"
  RBinder -> "lp-binder"
  RLogicVar -> "lp-var"
  RConst -> "lp-const"
  ROperator -> "lp-op"
  RPredicate -> "lp-pred"
  RTypeCon -> "lp-ty"
  RTyVar -> "lp-tyvar"
  RKindStar -> "lp-kind"
  RLiteral -> "lp-lit"
  RPi -> "lp-pi"
  RImpl -> "lp-impl"
  RPunct -> "lp-punct"
  RComment -> "lp-comment"
  RMetaKey -> "lp-key"
  RMetaVal -> "lp-val"

roleTip :: Role -> Text -> Text
roleTip r name = case r of
  RKeyword -> keywordTip name
  RModuleName -> "module name " <> name
  RBinder -> "binder " <> name <> " — a bound variable, visible in its scope"
  RLogicVar -> "logic variable " <> name <> " — unified during proof search"
  RConst -> constTip name
  ROperator -> operatorTip name
  RPredicate -> "predicate " <> name <> " — declared at type … → o"
  RTypeCon -> typeConTip name
  RTyVar -> "type variable " <> name <> " — prenex-polymorphic in this declaration"
  RKindStar -> "kind type — the kind of types"
  RLiteral -> "literal " <> name
  RPi ->
    if name == "sigma"
      then "existential goal (sigma): introduce a logic variable"
      else "universal goal (pi): introduce a fresh eigenvariable"
  RImpl -> "hypothetical implication (=>): left-hand clauses are added while proving the right-hand goal"
  RPunct -> punctTip name
  RComment -> "comment"
  RMetaKey -> "metadata key " <> name <> " — used by the example index and website"
  RMetaVal -> "metadata value"

constTip :: Text -> Text
constTip n = case n of
  "nil" -> "constant nil — the empty list"
  _ -> "constant " <> n <> " — a term constructor"

typeConTip :: Text -> Text
typeConTip n = case n of
  "o" -> "type o — the type of propositions and goals"
  "int" -> "type int — built-in integers"
  "string" -> "type string — built-in strings"
  "list" -> "type constructor list — the built-in list type"
  _ -> "type constructor " <> n

operatorTip :: Text -> Text
operatorTip n = case n of
  ":-" -> ":- — clause neck (the body implies the head)"
  "," -> ", — conjunction of goals"
  ";" -> "; — disjunction of goals"
  "::" -> ":: — list cons (infixr)"
  "=>" -> "=> — hypothetical implication"
  "=" -> "= — unification"
  "is" -> "is — evaluate the right-hand side and unify with the left"
  "+" -> "+ — integer addition"
  "-" -> "− — integer subtraction"
  "*" -> "* — integer multiplication"
  "div" -> "div — integer division"
  "mod" -> "mod — integer remainder"
  "^" -> "^ — string concatenation"
  "~" -> "~ — integer unary minus"
  "<" -> "< — integer comparison"
  ">" -> "> — integer comparison"
  "=<" -> "=< — integer comparison (≤)"
  ">=" -> ">= — integer comparison (≥)"
  _ -> "operator " <> n <> " — mixfix connective"

keywordTip :: Text -> Text
keywordTip kw = case kw of
  "module" -> "module — a collection of declarations and clauses"
  "sig" -> "sig — a signature (kinds and types without clauses)"
  "end" -> "end — optional terminator of a module or signature"
  "kind" -> "kind — declare a type constructor and its kind"
  "type" -> "type — declare a constant and its type"
  "typeabbrev" -> "typeabbrev — a type abbreviation"
  "accumulate" -> "accumulate — inline another module’s declarations"
  "accum_sig" -> "accum_sig — inline another signature"
  "import" -> "import — import a compiled module (source-level alias of accumulate here)"
  "local" -> "local — a constant not exported from this module"
  "localkind" -> "localkind — a kind not exported from this module"
  "closed" -> "closed — a constant that cannot be used as an eigenvariable"
  "exportdef" -> "exportdef — export a defined predicate"
  "useonly" -> "useonly — restrict the visible predicates of an accumulated module"
  "infix" -> "infix — non-associative mixfix declaration"
  "infixl" -> "infixl — left-associative infix operator"
  "infixr" -> "infixr — right-associative infix operator"
  "prefix" -> "prefix — prefix operator"
  "prefixr" -> "prefixr — right-associative prefix operator"
  "postfix" -> "postfix — postfix operator"
  "postfixl" -> "postfixl — left-associative postfix operator"
  "true" -> "true — the trivial goal, always succeeds"
  "fail" -> "fail — the empty goal, always fails"
  "not" -> "not — negation as failure (extra-logical)"
  "pi" -> "pi — universal goal: introduce a fresh eigenvariable"
  "sigma" -> "sigma — existential goal: introduce a logic variable"
  "!" -> "! — cut (commit to this clause)"
  _ -> "keyword " <> kw

punctTip :: Text -> Text
punctTip p = case p of
  "." -> ". — ends a declaration or clause"
  ":-" -> ":- — clause neck (the body implies the head)"
  "\\" -> "\\ — λ-abstraction (right-associative binder)"
  "->" -> "-> — function type (right-associative)"
  "::" -> ":: — list cons (infixr)"
  "," -> ", — conjunction of goals, or a list/declaration separator"
  ";" -> "; — disjunction of goals"
  "(" -> "( — grouping"
  ")" -> ") — grouping"
  "[" -> "[ — list literal"
  "]" -> "] — list literal"
  "|" -> "| — list tail separator"
  "=" -> "= — unification"
  ":" -> ": — type ascription on a binder"
  "!" -> "! — cut (commit to this clause)"
  _ -> operatorTip p

roleRank :: Role -> Int
roleRank r = case r of
  RMetaKey -> 12
  RMetaVal -> 11
  RBinder -> 10
  RPi -> 9
  RImpl -> 9
  RPredicate -> 8
  RTyVar -> 7
  RTypeCon -> 7
  RKindStar -> 7
  RModuleName -> 6
  RKeyword -> 6
  ROperator -> 5
  RLogicVar -> 4
  RConst -> 4
  RLiteral -> 3
  RPunct -> 2
  RComment -> 1

-- | Parse a file and attach both lexical and AST semantic marks.
annotateSource :: FilePath -> Text -> [Mark]
annotateSource file src =
  let lexMarks = marksSource file src
      astMarks =
        case parseModule file src of
          Left _ -> []
          Right m ->
            case mixfixModule defaultOps m of
              Left _ -> marksModule m
              Right m' -> marksModule m'
   in mergeMarks (lexMarks ++ astMarks)

mergeMarks :: [Mark] -> [Mark]
mergeMarks =
  map pick
    . groupBySpan
    . sortOn spanKey
  where
    spanKey mk =
      ( posLine (spanStart (markSpan mk))
      , posCol (spanStart (markSpan mk))
      , posLine (spanEnd (markSpan mk))
      , posCol (spanEnd (markSpan mk))
      )
    groupBySpan [] = []
    groupBySpan (m : ms) =
      let (eq, rest) = span (\x -> spanKey x == spanKey m) ms
       in (m : eq) : groupBySpan rest
    pick xs = last (sortOn (roleRank . markRole) xs)

--------------------------------------------------------------------------------
-- AST marks
--------------------------------------------------------------------------------

data AnnEnv = AnnEnv
  { aePreds :: Set Text
  }

collectEnv :: Module -> AnnEnv
collectEnv m =
  AnnEnv $
    Set.fromList $
      concatMap declPreds (modDecls m)
  where
    declPreds d = case d of
      DType ids ty | typeTargetsO ty -> map identName ids
      DExportDef ids (Just ty) | typeTargetsO ty -> map identName ids
      DExportDef ids Nothing -> map identName ids
      DUseOnly ids (Just ty) | typeTargetsO ty -> map identName ids
      DUseOnly ids Nothing -> map identName ids
      _ -> []

typeTargetsO :: SType -> Bool
typeTargetsO t = case t of
  STArr _ _ b -> typeTargetsO b
  STParen _ a -> typeTargetsO a
  STApp _ a _ -> typeTargetsO a
  STCon i -> identName i == "o"

marksModule :: Module -> [Mark]
marksModule m =
  let env = collectEnv m
      pre = modPreamble m
   in identMark RModuleName (modName m)
        : map
          (identMark RModuleName)
          (preAccumulate pre ++ preAccumSig pre ++ preImport pre ++ preUseSig pre)
        ++ concatMap (marksDecl env) (modDecls m)

marksDecl :: AnnEnv -> Decl -> [Mark]
marksDecl env d = case d of
  DKind ids k -> map (identMark RTypeCon) ids ++ marksKind k
  DType ids ty ->
    let r = if typeTargetsO ty then RPredicate else RConst
     in map (identMark r) ids ++ marksType ty
  DTypeAbbrev n args ty ->
    identMark RTypeCon n : map (identMark RTyVar) args ++ marksType ty
  DClause t -> marksTerm env Set.empty t
  DLocal ids mty ->
    map (identMark RConst) ids ++ maybe [] marksType mty
  DLocalKind ids mk ->
    map (identMark RTypeCon) ids ++ maybe [] marksKind mk
  DClosed ids mty ->
    map (identMark RConst) ids ++ maybe [] marksType mty
  DExportDef ids mty ->
    map (identMark RPredicate) ids ++ maybe [] marksType mty
  DUseOnly ids mty ->
    map (identMark RPredicate) ids ++ maybe [] marksType mty
  DFixity _ _ ids -> map (identMark ROperator) ids

marksKind :: SKind -> [Mark]
marksKind k = case k of
  SKType s -> [Mark s RKindStar (roleTip RKindStar "type")]
  SKArr _ a b -> marksKind a ++ marksKind b

marksType :: SType -> [Mark]
marksType t = case t of
  STCon i
    | isVar (identName i) -> [identMark RTyVar i]
    | identName i == "type" -> [identMark RKindStar i]
    | otherwise -> [identMark RTypeCon i]
  STArr _ a b -> marksType a ++ marksType b
  STApp _ a b -> marksType a ++ marksType b
  STParen _ a -> marksType a

marksTerm :: AnnEnv -> Set Text -> STerm -> [Mark]
marksTerm env bound t = case t of
  SId i
    | identName i `Set.member` bound -> [identMark RBinder i]
    | otherwise -> [identMark (idRole env i) i]
  SInt s n -> [Mark s RLiteral (roleTip RLiteral (T.pack (show n)))]
  SString s s' -> [Mark s RLiteral (roleTip RLiteral s')]
  SSeq _ xs -> concatMap (marksTerm env bound) xs
  SApp {} -> marksApp env bound t
  SLam _ x mty b ->
    identMark RBinder x
      : maybe [] marksType mty
      ++ marksTerm env (Set.insert (identName x) bound) b
  SList _ es tl -> concatMap (marksTerm env bound) es ++ maybe [] (marksTerm env bound) tl
  SParen _ a -> marksTerm env bound a
  SAnn _ a ty -> marksTerm env bound a ++ marksType ty
  SCut s -> [Mark s RKeyword (keywordTip "!")]

-- | @pi x y\\ G@ marks @x@ and @y@ as binders, not constants.
marksApp :: AnnEnv -> Set Text -> STerm -> [Mark]
marksApp env bound t =
  let (h, args) = viewApps t
   in case h of
        SId i
          | identName i `elem` ["pi", "sigma"] ->
              let (ids, rest) = span isId args
                  bound' = bound <> Set.fromList [identName b | SId b <- ids]
               in identMark RPi i
                    : [identMark RBinder b | SId b <- ids]
                    ++ concatMap (marksTerm env bound') rest
        _ ->
          marksTerm env bound h ++ concatMap (marksTerm env bound) args

viewApps :: STerm -> (STerm, [STerm])
viewApps = go []
  where
    go acc (SApp _ f a) = go (a : acc) f
    go acc u = (u, acc)

isId :: STerm -> Bool
isId (SId _) = True
isId _ = False

idRole :: AnnEnv -> Ident -> Role
idRole env i
  | n == "pi" || n == "sigma" = RPi
  | n == "=>" = RImpl
  | n `elem` ["true", "fail", "not"] = RKeyword
  | n `Map.member` defaultOps = ROperator
  | isVar n = RLogicVar
  | n `Set.member` aePreds env = RPredicate
  | otherwise = RConst
  where
    n = identName i

identMark :: Role -> Ident -> Mark
identMark r i = Mark (identLoc i) r (roleTip r (identName i))

isVar :: Text -> Bool
isVar t = case T.uncons t of
  Just (c, _) -> isUpper c || c == '_'
  Nothing -> False

--------------------------------------------------------------------------------
-- Lexical marks from raw source (keywords, comments, punctuation)
--------------------------------------------------------------------------------

keywords :: [Text]
keywords =
  [ "module"
  , "sig"
  , "end"
  , "kind"
  , "typeabbrev"
  , "type"
  , "accumulate"
  , "accum_sig"
  , "accumsig"
  , "import"
  , "use_sig"
  , "usesig"
  , "localkind"
  , "local"
  , "closed"
  , "exportdef"
  , "useonly"
  , "infixl"
  , "infixr"
  , "infix"
  , "prefixr"
  , "prefix"
  , "postfixl"
  , "postfix"
  ]

-- Longer keywords first so "typeabbrev" wins over "type".
keywordsLongest :: [Text]
keywordsLongest = sortOn (negate . T.length) keywords

marksSource :: FilePath -> Text -> [Mark]
marksSource file src = scan 1 1 (T.unpack src)
  where
    scan _ _ [] = []
    scan line col s@(c : rest)
      | c == '\n' = scan (line + 1) 1 rest
      | c == '%' =
          let (body, after) = span (/= '\n') s
              end = col + length body
              sp = mk file line col line end
              here = Mark sp RComment (roleTip RComment "") : commentKeys file line col body
           in here ++ scan line end after
      | take 2 s == "/*" =
          let (blk, after, el, ec) = takeBlock line col s
              sp = mk file line col el ec
           in Mark sp RComment (roleTip RComment "")
                : commentKeys file line col blk
                ++ scan el ec after
      | c == '"' =
          let (_lit, after, end) = takeString col s
              sp = mk file line col line end
           in Mark sp RLiteral (roleTip RLiteral "string") : scan line end after
      | isSpace c = scan line (col + 1) rest
      | Just (kw, rest') <- matchKeyword s =
          let end = col + T.length kw
              sp = mk file line col line end
           in Mark sp RKeyword (keywordTip kw) : scan line end rest'
      | Just (op, rest') <- matchPunct s =
          let end = col + T.length op
              sp = mk file line col line end
           in Mark sp RPunct (punctTip op) : scan line end rest'
      | isIdentChar c =
          let n = length (takeWhile isIdentChar s)
           in scan line (col + n) (drop n s)
      | otherwise = scan line (col + 1) rest

    takeString col ('"' : xs) =
      let (inner, rest) = span (/= '"') xs
          n = 1 + length inner + if take 1 rest == "\"" then 1 else 0
          after = if take 1 rest == "\"" then drop 1 rest else rest
       in (inner, after, col + n)
    takeString col xs = ("", xs, col)

    takeBlock line col s =
      case breakBlock line col s 0 of
        (el, ec, after, n) -> (take n s, after, el, ec)

    breakBlock line col [] n = (line, col, [], n)
    breakBlock line col ('*' : '/' : rest) n = (line, col + 2, rest, n + 2)
    breakBlock line _col ('\n' : rest) n = breakBlock (line + 1) 1 rest (n + 1)
    breakBlock line col (_ : rest) n = breakBlock line (col + 1) rest (n + 1)

mk :: FilePath -> Int -> Int -> Int -> Int -> SrcSpan
mk file sl sc el ec =
  SrcSpan file (SrcPos sl sc 0) (SrcPos el ec 0)

matchKeyword :: String -> Maybe (Text, String)
matchKeyword s =
  case
    [ (kw, after)
    | kw <- keywordsLongest
    , kw `T.isPrefixOf` T.pack s
    , let after = drop (T.length kw) s
    , case after of
        [] -> True
        (a : _) -> not (isIdentChar a)
    ] of
    (h : _) -> Just h
    [] -> Nothing

matchPunct :: String -> Maybe (Text, String)
matchPunct s =
  case
    [ (T.pack p, drop (length p) s)
    | p <-
        [ "->"
        , ":-"
        , "::"
        , "=>"
        , "=<"
        , ">="
        , "\\"
        , "."
        , ","
        , ";"
        , "("
        , ")"
        , "["
        , "]"
        , "|"
        , "="
        , ":"
        , "!"
        , "+"
        , "-"
        , "*"
        , "^"
        , "~"
        , "<"
        , ">"
        ]
    , T.pack p `T.isPrefixOf` T.pack s
    ] of
    (h : _) -> Just h
    [] -> Nothing

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

-- | Highlight @key:@ / value pairs at the start of a comment payload
-- (@% title: …@ or @/* tags: … */@).
commentKeys :: FilePath -> Int -> Int -> String -> [Mark]
commentKeys file line col0 body =
  let text = T.takeWhile (/= '\n') (T.pack body)
      payload =
        T.dropWhile isSpace $
          case T.stripPrefix "/*" text of
            Just inner -> inner
            Nothing -> T.dropWhile (== '%') text
      stripped' = T.dropWhile isSpace payload
   in case T.break (== ':') stripped' of
        (key, rest)
          | T.length key > 0
              && T.length key <= 24
              && T.all (\c -> isLower c || c == '_' || c == '-') key
              && not (T.null rest)
              , let needle = key <> ":"
              , let (pre, more) = T.breakOn needle text
              , not (T.null more) ->
              let keyStart = col0 + T.length pre
                  keyEnd = keyStart + T.length needle
                  valRaw = T.drop (keyEnd - col0) text
                  valKept =
                    T.dropWhileEnd isSpace $
                      if "*/" `T.isSuffixOf` T.stripEnd valRaw
                        then T.dropEnd 2 (T.stripEnd valRaw)
                        else valRaw
                  valStart = keyEnd
                  valEnd = keyEnd + T.length valKept
               in [ Mark (mk file line keyStart line keyEnd) RMetaKey (roleTip RMetaKey needle)
                  , Mark (mk file line valStart line valEnd) RMetaVal (roleTip RMetaVal "")
                  ]
        _ -> []
