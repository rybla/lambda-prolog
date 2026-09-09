-- | User-facing errors. Kernel failures (unification, search) are converted
-- into this type at the driver boundary so the CLI has one printer.
module LambdaProlog.Error
  ( Error (..)
  , mkError
  , mkErrorAt
  , prettyError
  , renderError
  ) where

import Data.Text (Text)
import Prettyprinter (Doc, defaultLayoutOptions, layoutPretty, pretty, vsep, (<+>))
import Prettyprinter.Render.Text (renderStrict)

import LambdaProlog.Span (SrcSpan, prettySpan)

data Error = Error
  { errorSpan :: Maybe SrcSpan
  , errorMessage :: Text
  , errorContext :: [Text]
  }
  deriving stock (Eq, Show)

mkError :: Text -> Error
mkError msg = Error Nothing msg []

mkErrorAt :: SrcSpan -> Text -> Error
mkErrorAt sp msg = Error (Just sp) msg []

prettyError :: Error -> Doc ann
prettyError err =
  case errorSpan err of
    Nothing -> pretty (errorMessage err) <> contextDocs
    Just sp ->
      prettySpan sp
        <> pretty ':'
        <+> pretty (errorMessage err)
        <> contextDocs
  where
    contextDocs =
      case errorContext err of
        [] -> mempty
        cs -> pretty '\n' <> vsep (map pretty cs)

renderError :: Error -> Text
renderError = renderStrict . layoutPretty defaultLayoutOptions . prettyError
