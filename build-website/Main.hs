-- | Build a static HTML site for lambda-prolog into @website/@, suitable for
-- GitHub Pages.
module Main (main) where

import Data.List (sort)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (createDirectoryIfMissing, listDirectory)
import System.FilePath (takeBaseName, takeExtension, (</>))

import Assets (css, faviconSvg, js)
import Highlight (Header (..), highlight, parseHeader)
import Html (Html, el, fromHtml, page, txt)

main :: IO ()
main = do
  let root = "website"
  createDirectoryIfMissing True (root </> "css")
  createDirectoryIfMissing True (root </> "js")
  createDirectoryIfMissing True (root </> "examples")
  TIO.writeFile (root </> "css" </> "site.css") css
  TIO.writeFile (root </> "js" </> "site.js") js
  TIO.writeFile (root </> "favicon.svg") faviconSvg
  files <- fmap (sort . filter isMod) (listDirectory "examples")
  exs <- mapM loadExample files
  TIO.writeFile (root </> "index.html") (fromHtml indexPage)
  TIO.writeFile (root </> "examples" </> "index.html") (fromHtml (examplesIndex exs))
  mapM_ (writeExample root) exs
  putStrLn $ "wrote " ++ show (length exs) ++ " example pages to website/"

isMod :: FilePath -> Bool
isMod f = takeExtension f == ".mod"

data Example = Example
  { exFile :: FilePath
  , exSlug :: String
  , exSrc :: Text
  , exHeader :: Header
  }

loadExample :: FilePath -> IO Example
loadExample f = do
  src <- TIO.readFile ("examples" </> f)
  pure $
    Example
      { exFile = f
      , exSlug = takeBaseName f
      , exSrc = src
      , exHeader = parseHeader src
      }

writeExample :: FilePath -> Example -> IO ()
writeExample root ex =
  TIO.writeFile
    (root </> "examples" </> exSlug ex ++ ".html")
    (fromHtml (examplePage ex))

nav :: Text -> Html
nav root =
  el "header" [] $
    el "nav" [] $
      el "a" [("href", root <> "index.html")] (txt "λProlog")
        <> txt " · "
        <> el "a" [("href", root <> "examples/index.html")] (txt "Examples")

indexPage :: Html
indexPage =
  page "" "λProlog in Haskell" "A higher-order hereditary Harrop interpreter" $
    nav ""
      <> el
        "main"
        []
        ( el "h1" [] (txt "λProlog")
            <> el
              "p"
              []
              ( txt "A Haskell interpreter for the higher-order hereditary Harrop fragment of λProlog: simply-typed λ-terms, pattern unification, and uniform proof search with "
                  <> el "code" [] (txt "pi")
                  <> txt " and "
                  <> el "code" [] (txt "=>")
                  <> txt "."
              )
            <> el "h2" [] (txt "What this is")
            <> el
              "p"
              []
              ( txt "Hereditary Harrop formulas extend Horn clauses with implication and universal quantification in goals. Operationally that means a program is not a flat clause store: proving "
                  <> el "code" [] (txt "D => G")
                  <> txt " installs "
                  <> el "code" [] (txt "D")
                  <> txt " for the duration of "
                  <> el "code" [] (txt "G")
                  <> txt ", and proving "
                  <> el "code" [] (txt "pi x\\ G")
                  <> txt " introduces a fresh eigenvariable. Nested programs and signatures are the hierarchical structure unique to this language."
              )
            <> el "h2" [] (txt "Build")
            <> el
              "pre"
              [("class", "src")]
              ( txt "stack build\nstack test\nstack run lambda-prolog -- examples/lists.mod\nstack run build-website"
              )
            <> el
              "p"
              []
              ( el "a" [("href", "examples/index.html")] (txt "Browse the examples")
                  <> txt " — hover any token on an example page for its role."
              )
            <> el "h2" [] (txt "References")
            <> el
              "ul"
              []
              ( el "li" [] (el "a" [("href", "https://sites.google.com/site/proghol/")] (txt "Programming with Higher-Order Logic") <> txt " — Miller & Nadathur")
                  <> el "li" [] (el "a" [("href", "https://teyjus.cs.umn.edu")] (txt "Teyjus"))
                  <> el "li" [] (el "a" [("href", "https://github.com/LPCIC/elpi")] (txt "ELPI"))
              )
        )

examplesIndex :: [Example] -> Html
examplesIndex exs =
  page "../" "Examples — λProlog" "Example programs" $
    nav "../"
      <> el
        "main"
        []
        ( el "h1" [] (txt "Examples")
            <> el "p" [("class", "muted")] (txt "Click through for semantically highlighted source.")
            <> el "div" [("class", "cards")] (foldMap card exs)
        )
  where
    card ex =
      el "article" [("class", "card")] $
        el "h2" [] (el "a" [("href", T.pack (exSlug ex ++ ".html"))] (txt (hdrTitle (exHeader ex))))
          <> el "p" [] (txt (hdrSummary (exHeader ex)))
          <> el "p" [("class", "tags")] (foldMap (\t -> el "span" [] (txt t)) (hdrTags (exHeader ex)))

examplePage :: Example -> Html
examplePage ex =
  page "../" (hdrTitle (exHeader ex) <> " — λProlog") (hdrSummary (exHeader ex)) $
    nav "../"
      <> el
        "main"
        []
        ( el "h1" [] (txt (hdrTitle (exHeader ex)))
            <> el "p" [] (txt (hdrSummary (exHeader ex)))
            <> el "p" [("class", "muted")] (txt (T.pack (exFile ex)))
            <> el
              "p"
              [("class", "legend")]
              ( legend "lp-kw" "keyword"
                  <> legend "lp-pred" "predicate"
                  <> legend "lp-ty" "type"
                  <> legend "lp-tyvar" "type variable"
                  <> legend "lp-var" "variable"
                  <> legend "lp-binder" "binder"
                  <> legend "lp-const" "constant"
                  <> legend "lp-op" "operator"
                  <> legend "lp-pi" "pi"
                  <> legend "lp-impl" "=>"
                  <> legend "lp-punct" "punctuation"
                  <> legend "lp-key" "title:"
              )
            <> highlight ("examples/" ++ exFile ex) (exSrc ex)
        )
  where
    legend cls lab =
      el "span" [] (el "i" [("class", cls)] (txt lab))

