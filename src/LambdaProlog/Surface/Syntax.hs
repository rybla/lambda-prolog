-- | Surface syntax: modules, declarations, and pre-mixfix terms with source
-- spans. Mixfix resolution (Fixity) turns 'SSeq' into applications.
module LambdaProlog.Surface.Syntax
  ( Ident (..)
  , identText
  , identSpan
  , SKind (..)
  , SType (..)
  , FixityKind (..)
  , STerm (..)
  , termSpan
  , Decl (..)
  , Preamble (..)
  , ModuleKind (..)
  , Module (..)
  ) where

import Data.Text (Text)

import LambdaProlog.Span (SrcSpan)

-- | A surface identifier. Capitalization is preserved; classification into
-- constants vs logic variables happens during elaboration.
data Ident = Ident
  { identName :: Text
  , identLoc :: SrcSpan
  }
  deriving stock (Eq, Show)

identText :: Ident -> Text
identText = identName

identSpan :: Ident -> SrcSpan
identSpan = identLoc

data SKind
  = SKType SrcSpan
  | SKArr SrcSpan SKind SKind
  deriving stock (Eq, Show)

data SType
  = STCon Ident
  | STArr SrcSpan SType SType
  | STApp SrcSpan SType SType
  | STParen SrcSpan SType
  deriving stock (Eq, Show)

data FixityKind
  = FxInfix
  | FxInfixl
  | FxInfixr
  | FxPrefix
  | FxPostfix
  deriving stock (Eq, Ord, Show)

-- | Pre- and post-mixfix terms. 'SSeq' is juxtaposition as produced by the
-- parser; the mixfix pass eliminates it.
data STerm
  = SId Ident
  | SInt SrcSpan Integer
  | SString SrcSpan Text
  | SSeq SrcSpan [STerm]
  | SApp SrcSpan STerm STerm
  | SLam SrcSpan Ident (Maybe SType) STerm
  | SList SrcSpan [STerm] (Maybe STerm)
  | SParen SrcSpan STerm
  | SAnn SrcSpan STerm SType
  | SCut SrcSpan
  deriving stock (Eq, Show)

termSpan :: STerm -> SrcSpan
termSpan t = case t of
  SId i -> identLoc i
  SInt s _ -> s
  SString s _ -> s
  SSeq s _ -> s
  SApp s _ _ -> s
  SLam s _ _ _ -> s
  SList s _ _ -> s
  SParen s _ -> s
  SAnn s _ _ -> s
  SCut s -> s

data Decl
  = DKind [Ident] SKind
  | DType [Ident] SType
  | DTypeAbbrev Ident [Ident] SType
  | DFixity FixityKind Int [Ident]
  | DLocal [Ident] (Maybe SType)
  | DLocalKind [Ident] (Maybe SKind)
  | DClosed [Ident] (Maybe SType)
  | DExportDef [Ident] (Maybe SType)
  | DUseOnly [Ident] (Maybe SType)
  | DClause STerm
  deriving stock (Eq, Show)

data Preamble = Preamble
  { preAccumulate :: [Ident]
  , preAccumSig :: [Ident]
  , preImport :: [Ident]
  , preUseSig :: [Ident]
  }
  deriving stock (Eq, Show)

data ModuleKind = MKModule | MKSignature
  deriving stock (Eq, Show)

data Module = Module
  { modKind :: ModuleKind
  , modName :: Ident
  , modPreamble :: Preamble
  , modDecls :: [Decl]
  , modSpan :: SrcSpan
  }
  deriving stock (Eq, Show)
