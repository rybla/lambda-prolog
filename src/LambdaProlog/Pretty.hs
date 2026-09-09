-- | Shared pretty-printer rendering helpers.
module LambdaProlog.Pretty
  ( renderDoc
  , renderDocUnlined
  ) where

import Data.Text (Text)
import Prettyprinter
  ( Doc
  , LayoutOptions (..)
  , PageWidth (..)
  , defaultLayoutOptions
  , layoutPretty
  )
import Prettyprinter.Render.Text (renderStrict)

renderDoc :: Doc ann -> Text
renderDoc = renderStrict . layoutPretty defaultLayoutOptions

-- | Render with unbounded page width so answer substitutions stay on one line.
renderDocUnlined :: Doc ann -> Text
renderDocUnlined =
  renderStrict . layoutPretty (defaultLayoutOptions {layoutPageWidth = Unbounded})
