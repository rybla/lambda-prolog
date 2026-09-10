-- | Megaparsec parser for Teyjus-style λProlog modules and signatures.
module LambdaProlog.Surface.Parser
  ( parseModule
  , parseTerm
  , parseQuery
  ) where

import Control.Monad (void)
import Data.Char (isAlphaNum, isLower, isSpace, isUpper)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
  ( Parsec
  , SourcePos (..)
  , between
  , choice
  , eof
  , errorBundlePretty
  , getSourcePos
  , many
  , manyTill
  , notFollowedBy
  , option
  , optional
  , parse
  , satisfy
  , sepBy
  , sepBy1
  , some
  , try
  , unPos
  , (<?>)
  , (<|>)
  )
import Text.Megaparsec.Char (char, string)
import Text.Megaparsec.Char.Lexer qualified as L

import LambdaProlog.Error (Error, mkError)
import LambdaProlog.Span (SrcPos (..), SrcSpan (..), combineSpans)
import LambdaProlog.Surface.Syntax

type Parser = Parsec Void Text

parseModule :: FilePath -> Text -> Either Error Module
parseModule file src =
  case parse (sc *> pFile <* eof) file src of
    Left e -> Left (mkError (T.pack (errorBundlePretty e)))
    Right m -> Right m {modSpan = (modSpan m) {spanFile = file}}

parseTerm :: FilePath -> Text -> Either Error STerm
parseTerm file src =
  case parse (sc *> pTerm <* optional (symbol ".") <* eof) file src of
    Left e -> Left (mkError (T.pack (errorBundlePretty e)))
    Right t -> Right t

parseQuery :: FilePath -> Text -> Either Error STerm
parseQuery file src =
  case parse (sc *> optional (symbol "?-") *> pTerm <* optional (symbol ".") <* eof) file src of
    Left e -> Left (mkError (T.pack (errorBundlePretty e)))
    Right t -> Right t

--------------------------------------------------------------------------------
-- Space and spans
--------------------------------------------------------------------------------

sc :: Parser ()
sc = L.space (void (satisfy isSpace)) (L.skipLineComment "%") (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

withSpan :: Parser a -> Parser (SrcSpan, a)
withSpan p = do
  file <- sourceName <$> getSourcePos
  start <- getSourcePos
  a <- p
  end <- getSourcePos
  pure (mkSpan file start end, a)

mkSpan :: FilePath -> SourcePos -> SourcePos -> SrcSpan
mkSpan file s e =
  SrcSpan
    file
    (SrcPos (unPos (sourceLine s)) (unPos (sourceColumn s)) 0)
    (SrcPos (unPos (sourceLine e)) (unPos (sourceColumn e)) 0)

--------------------------------------------------------------------------------
-- Tokens
--------------------------------------------------------------------------------

keywords :: [Text]
keywords =
  [ "module"
  , "sig"
  , "end"
  , "kind"
  , "type"
  , "typeabbrev"
  , "accumulate"
  , "accum_sig"
  , "accumsig"
  , "import"
  , "use_sig"
  , "usesig"
  , "local"
  , "localkind"
  , "closed"
  , "exportdef"
  , "useonly"
  , "infix"
  , "infixl"
  , "infixr"
  , "prefix"
  , "prefixr"
  , "postfix"
  , "postfixl"
  , "query"
  , "succeeds"
  , "fails"
  , "sample"
  ]

isIdentStart :: Char -> Bool
isIdentStart c = isLower c || isUpper c || c == '_'

isIdentCont :: Char -> Bool
isIdentCont c = isAlphaNum c || c `elem` ("_'" :: String)

pWordRaw :: Parser Text
pWordRaw = do
  c <- satisfy isIdentStart <?> "identifier"
  rest <- many (satisfy isIdentCont)
  let txt = T.pack (c : rest)
  if txt `elem` keywords
    then fail ("unexpected keyword " <> T.unpack txt)
    else pure txt

pSymbolicRaw :: Parser Text
pSymbolicRaw = T.pack <$> some (satisfy isSym)
  where
    -- Intentionally not ',' ';' '|' '\\' — those are separators / binders.
    isSym c = c `elem` ("+-*/<=>&@#`~?!$:^" :: String)

pIdent :: Parser Ident
pIdent = lexeme $ do
  (sp, n) <- withSpan (try pWordRaw <|> pSymbolicRaw)
  pure (Ident n sp)

pKeyword :: Text -> Parser ()
pKeyword kw =
  lexeme . try $ do
    _ <- string kw
    notFollowedBy (satisfy isIdentCont)

pNumber :: Parser (SrcSpan, Integer)
pNumber = lexeme (withSpan L.decimal)

pStringLit :: Parser (SrcSpan, Text)
pStringLit =
  lexeme $
    withSpan $ do
      _ <- char '"'
      T.pack <$> manyTill L.charLiteral (char '"')

--------------------------------------------------------------------------------
-- File
--------------------------------------------------------------------------------

pFile :: Parser Module
pFile = do
  file <- sourceName <$> getSourcePos
  start <- getSourcePos
  (kind, name) <- pHeader
  pre <- pPreamble
  decls <- many pDecl
  _ <- optional (pKeyword "end")
  end <- getSourcePos
  pure
    Module
      { modKind = kind
      , modName = name
      , modPreamble = pre
      , modDecls = decls
      , modSpan = mkSpan file start end
      }

pHeader :: Parser (ModuleKind, Ident)
pHeader =
  choice
    [ try $ do
        pKeyword "module"
        n <- pIdent
        _ <- symbol "."
        pure (MKModule, n)
    , try $ do
        pKeyword "sig"
        n <- pIdent
        _ <- symbol "."
        pure (MKSignature, n)
    , do
        pos <- getSourcePos
        let sp = mkSpan (sourceName pos) pos pos
        pure (MKModule, Ident "" sp)
    ]

pPreamble :: Parser Preamble
pPreamble = go (Preamble [] [] [] [])
  where
    go pre =
      choice
        [ do
            pKeyword "accumulate"
            ids <- pIdList
            _ <- symbol "."
            go pre {preAccumulate = preAccumulate pre ++ ids}
        , do
            try (pKeyword "accum_sig") <|> pKeyword "accumsig"
            ids <- pIdList
            _ <- symbol "."
            go pre {preAccumSig = preAccumSig pre ++ ids}
        , do
            pKeyword "import"
            ids <- pIdList
            _ <- symbol "."
            go pre {preImport = preImport pre ++ ids}
        , do
            try (pKeyword "use_sig") <|> pKeyword "usesig"
            ids <- pIdList
            _ <- symbol "."
            go pre {preUseSig = preUseSig pre ++ ids}
        , pure pre
        ]

pIdList :: Parser [Ident]
pIdList = sepBy1 pIdent (symbol ",")

pDecl :: Parser Decl
pDecl =
  choice
    [ try pKindDecl
    , try pTypeAbbrev
    , try pTypeDecl
    , try pFixityDecl
    , try pLocalKind
    , try pLocal
    , try pClosed
    , try pExportDef
    , try pUseOnly
    , try pQueryDecl
    , pClause
    ]

pKindDecl :: Parser Decl
pKindDecl = do
  pKeyword "kind"
  ids <- pIdList
  k <- pKind
  _ <- symbol "."
  pure (DKind ids k)

pTypeDecl :: Parser Decl
pTypeDecl = do
  pKeyword "type"
  ids <- pIdList
  t <- pType
  _ <- symbol "."
  pure (DType ids t)

pTypeAbbrev :: Parser Decl
pTypeAbbrev = do
  pKeyword "typeabbrev"
  (name, args) <-
    choice
      [ try $
          between (symbol "(") (symbol ")") $ do
            n <- pIdent
            as <- many pIdent
            pure (n, as)
      , do
          n <- pIdent
          pure (n, [])
      ]
  t <- pType
  _ <- symbol "."
  pure (DTypeAbbrev name args t)

pFixityDecl :: Parser Decl
pFixityDecl = do
  fx <- pFixityKw
  ids <- pIdList
  (_, n) <- pNumber
  _ <- symbol "."
  pure (DFixity fx (fromInteger n) ids)

pFixityKw :: Parser FixityKind
pFixityKw =
  choice
    [ FxInfixl <$ pKeyword "infixl"
    , FxInfixr <$ pKeyword "infixr"
    , FxInfix <$ pKeyword "infix"
    , FxPrefix <$ pKeyword "prefixr"
    , FxPrefix <$ pKeyword "prefix"
    , FxPostfix <$ pKeyword "postfixl"
    , FxPostfix <$ pKeyword "postfix"
    ]

pLocal :: Parser Decl
pLocal = do
  pKeyword "local"
  ids <- pIdList
  t <- optional pType
  _ <- symbol "."
  pure (DLocal ids t)

pLocalKind :: Parser Decl
pLocalKind = do
  pKeyword "localkind"
  ids <- pIdList
  k <- optional pKind
  _ <- symbol "."
  pure (DLocalKind ids k)

pClosed :: Parser Decl
pClosed = do
  pKeyword "closed"
  ids <- pIdList
  t <- optional pType
  _ <- symbol "."
  pure (DClosed ids t)

pExportDef :: Parser Decl
pExportDef = do
  pKeyword "exportdef"
  ids <- pIdList
  t <- optional pType
  _ <- symbol "."
  pure (DExportDef ids t)

pUseOnly :: Parser Decl
pUseOnly = do
  pKeyword "useonly"
  ids <- pIdList
  t <- optional pType
  _ <- symbol "."
  pure (DUseOnly ids t)

pClause :: Parser Decl
pClause = do
  t <- pTerm
  _ <- symbol "."
  pure (DClause t)

pQueryDecl :: Parser Decl
pQueryDecl = do
  pKeyword "query"
  opts <- pQueryOptions
  _ <- try (symbol "?-") <|> symbol "?"
  t <- pTerm
  _ <- symbol "."
  pure (DQuery opts t)

pQueryOptions :: Parser [QueryOption]
pQueryOptions =
  choice
    [ try $ between (symbol "[") (symbol "]") (pOption `sepBy` optional (symbol ","))
    , try $ between (symbol "(") (symbol ")") (pOption `sepBy` optional (symbol ","))
    , many (try pOption)
    ]

pOption :: Parser QueryOption
pOption =
  choice
    [ QOSucceeds <$ pKeyword "succeeds"
    , QOFails <$ pKeyword "fails"
    , pSample
    ]

pSample :: Parser QueryOption
pSample = do
  pKeyword "sample"
  n <- choice
    [ between (symbol "(") (symbol ")") L.decimal
    , lexeme L.decimal
    ]
  pure (QOSample (fromInteger n))

--------------------------------------------------------------------------------
-- Kinds and types
--------------------------------------------------------------------------------

pKind :: Parser SKind
pKind = do
  a <- pKindAtom
  option a $ do
    _ <- symbol "->"
    b <- pKind
    pure (SKArr (kindSpan a) a b)

pKindAtom :: Parser SKind
pKindAtom =
  choice
    [ do
        -- Span the word only (not the trailing space that 'lexeme' would eat)
        -- so it coincides with the lexical keyword mark.
        (sp, _) <- withSpan $ try $ do
          _ <- string "type"
          notFollowedBy (satisfy isIdentCont)
        sc
        pure (SKType sp)
    , between (symbol "(") (symbol ")") pKind
    ]

kindSpan :: SKind -> SrcSpan
kindSpan (SKType s) = s
kindSpan (SKArr s _ _) = s

pType :: Parser SType
pType = do
  a <- pTyApp
  option a $ do
    _ <- symbol "->"
    b <- pType
    pure (STArr (typeSpan a) a b)

pTyApp :: Parser SType
pTyApp = do
  xs <- some pTyAtom
  pure (foldl1 (\l r -> STApp (typeSpan l) l r) xs)

pTyAtom :: Parser SType
pTyAtom =
  choice
    [ try $ do
        i <- pIdent
        if identName i == "->"
          then fail "type arrow"
          else pure (STCon i)
    , between (symbol "(") (symbol ")") pType
    ]

typeSpan :: SType -> SrcSpan
typeSpan t = case t of
  STCon i -> identLoc i
  STArr s _ _ -> s
  STApp s _ _ -> s
  STParen s _ -> s

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

pTerm :: Parser STerm
pTerm = do
  xs <- some pAbsTerm
  case xs of
    [x] -> pure x
    x : rest ->
      let sp = combineSpans (termSpan x) (termSpan (lastOf x rest))
       in pure (SSeq sp xs)
    [] -> error "unreachable"

pAbsTerm :: Parser STerm
pAbsTerm = try pLam <|> pAtom

pAbsTermNoSep :: Parser STerm
pAbsTermNoSep = try pLam <|> pAtomNoSep

pLam :: Parser STerm
pLam = do
  file <- sourceName <$> getSourcePos
  start <- getSourcePos
  x <- pIdent
  ty <- optional (pAscribeColon *> pType)
  _ <- symbol "\\"
  body <- pTerm
  end <- getSourcePos
  pure (SLam (mkSpan file start end) x ty body)

-- | Type ascription colon, not the start of @:-@.
pAscribeColon :: Parser Text
pAscribeColon =
  lexeme . try $ do
    _ <- char ':'
    notFollowedBy (char '-')
    pure ":"

pAtom :: Parser STerm
pAtom = pAtomNoSep <|> (SId <$> pCommaSemi)

pAtomNoSep :: Parser STerm
pAtomNoSep =
  choice
    [ SCut . fst <$> withSpan (symbol "!")
    , uncurry SInt <$> pNumber
    , uncurry SString <$> pStringLit
    , try pList
    , between (symbol "(") (symbol ")") pTerm
    , SId <$> pIdent
    ]

pCommaSemi :: Parser Ident
pCommaSemi = lexeme $ do
  (sp, n) <-
    withSpan $
      choice
        [ "," <$ char ','
        , ";" <$ char ';'
        ]
  pure (Ident n sp)

pList :: Parser STerm
pList = do
  file <- sourceName <$> getSourcePos
  start <- getSourcePos
  _ <- symbol "["
  contents <-
    optional $ do
      e <- pListElem
      es <- many (symbol "," *> pListElem)
      tl <- optional (symbol "|" *> pTerm)
      pure (e : es, tl)
  _ <- symbol "]"
  end <- getSourcePos
  let sp = mkSpan file start end
  pure $ case contents of
    Nothing -> SList sp [] Nothing
    Just (es, tl) -> SList sp es tl

-- | Juxtaposition that does not consume list separators.
pListElem :: Parser STerm
pListElem = do
  xs <- some pAbsTermNoSep
  case xs of
    [x] -> pure x
    x : rest ->
      let sp = combineSpans (termSpan x) (termSpan (lastOf x rest))
       in pure (SSeq sp xs)
    [] -> error "unreachable"

lastOf :: a -> [a] -> a
lastOf x [] = x
lastOf _ (y : ys) = lastOf y ys
