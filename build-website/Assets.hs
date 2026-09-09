{-# LANGUAGE QuasiQuotes #-}

-- | Stylesheet, script, and favicon for the static site. Semantic colour is
-- defined once as custom properties and reused on every page.
module Assets
  ( css
  , js
  , faviconSvg
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Text.RawString.QQ (r)

css :: Text
css = [r|
/* TODO: CSS asset */
|]

js :: Text
js = [r|
// TODO: JavaScript asset
|]

faviconSvg :: Text
faviconSvg = undefined
