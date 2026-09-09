-- | Source locations. Every surface-syntax node carries a 'SrcSpan'; kernel
-- terms constructed by elaboration or the engine use 'dummySpan'.
module LambdaProlog.Span
  ( SrcPos (..)
  , SrcSpan (..)
  , Located (..)
  , dummyPos
  , dummySpan
  , located
  , unLocated
  , spanOf
  , combineSpans
  , prettySpan
  , spanText
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Prettyprinter (Doc, pretty)

-- | 1-based line and column, 0-based character offset into the file.
data SrcPos = SrcPos
  { posLine :: Int
  , posCol :: Int
  , posOffset :: Int
  }
  deriving stock (Eq, Ord, Show)

data SrcSpan = SrcSpan
  { spanFile :: FilePath
  , spanStart :: SrcPos
  , spanEnd :: SrcPos
  }
  deriving stock (Eq, Ord, Show)

data Located a = Located
  { locatedSpan :: SrcSpan
  , locatedValue :: a
  }
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

dummyPos :: SrcPos
dummyPos = SrcPos 1 1 0

dummySpan :: SrcSpan
dummySpan = SrcSpan "" dummyPos dummyPos

located :: SrcSpan -> a -> Located a
located = Located

unLocated :: Located a -> a
unLocated = locatedValue

spanOf :: Located a -> SrcSpan
spanOf = locatedSpan

-- | Smallest span covering both arguments. Prefers the left file name.
combineSpans :: SrcSpan -> SrcSpan -> SrcSpan
combineSpans a b =
  SrcSpan
    { spanFile = spanFile a
    , spanStart = min (spanStart a) (spanStart b)
    , spanEnd = max (spanEnd a) (spanEnd b)
    }

prettySpan :: SrcSpan -> Doc ann
prettySpan s =
  pretty (spanFile s)
    <> pretty ':'
    <> pretty (posLine (spanStart s))
    <> pretty ':'
    <> pretty (posCol (spanStart s))

-- | Compact @file:line:col@ form, used in error messages.
spanText :: SrcSpan -> Text
spanText s =
  T.pack (spanFile s)
    <> ":"
    <> T.pack (show (posLine (spanStart s)))
    <> ":"
    <> T.pack (show (posCol (spanStart s)))
