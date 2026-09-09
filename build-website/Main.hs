-- | Build a static HTML site for lambda-prolog into @website/@, suitable for
-- GitHub Pages.
module Main (main) where

import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))

import Assets (css, faviconSvg, js)
import Html (fromHtml)

main :: IO ()
main = do
  let root = "website"
  createDirectoryIfMissing True (root </> "css")
  createDirectoryIfMissing True (root </> "js")
  createDirectoryIfMissing True (root </> "examples")
  -- TODO
  undefined
