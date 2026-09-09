-- | Wrap original source in nested semantic spans.
module Highlight
  ( highlight
  , parseHeader
  , Header (..)
  ) where

import Data.Char (isSpace)
import Data.List (sortOn)
import Data.Text (Text)
import Data.Text qualified as T

import Html (Html, el, raw, txt)
import LambdaProlog.Span (SrcPos (..), SrcSpan (..))
import LambdaProlog.Surface.Annotate (Mark (..), Role (..), marksModule, roleClass)
import LambdaProlog.Surface.Fixity (defaultOps, mixfixModule)
import LambdaProlog.Surface.Parser (parseModule)
import LambdaProlog.Surface.Syntax (Module)

data Header = Header
  { hdrTitle :: Text
  , hdrTags :: [Text]
  , hdrSummary :: Text
  }

parseHeader :: Text -> Header
parseHeader src =
  let ls = take 10 (T.lines src)
      grab key =
        let p = "% " <> key <> ":"
         in case [T.strip (T.drop (T.length p) l) | l <- ls, p `T.isPrefixOf` l] of
              (x : _) -> x
              [] -> ""
      tags = [t | t <- T.splitOn "," (grab "tags"), not (T.null (T.strip t))]
   in Header
        { hdrTitle = nonempty (grab "title") "Example"
        , hdrTags = map T.strip tags
        , hdrSummary = nonempty (grab "summary") ""
        }
  where
    nonempty t d = if T.null t then d else t

highlight :: FilePath -> Text -> Html
highlight file src =
  case parseModule file src of
    Left _ -> el "pre" [("class", "src")] (txt src)
    Right m ->
      case mixfixModule defaultOps m of
        Left _ -> el "pre" [("class", "src")] (txt src)
        Right m' ->
          el "pre" [("class", "src")] (paint src (marksModule m'))

paint :: Text -> [Mark] -> Html
paint src marks =
  let indexed = zip [1 ..] (T.lines src)
      -- Paint line by line; marks that cover a token on that line wrap it.
      lineHtml (n, line) =
        let here =
              [ mk
              | mk <- marks
              , posLine (spanStart (markSpan mk)) == n
              ]
         in paintLine line n here <> raw "\n"
   in foldMap lineHtml indexed

paintLine :: Text -> Int -> [Mark] -> Html
paintLine line _ [] = txt line
paintLine line lineNo marks =
  let sorted = sortOn (\mk -> posCol (spanStart (markSpan mk))) marks
   in go 1 sorted line
  where
    go _ [] rest = txt rest
    go col (mk : ms) rest =
      let start = posCol (spanStart (markSpan mk))
          end = posCol (spanEnd (markSpan mk))
          relS = max 0 (start - col)
          relE = max relS (end - col)
          (pre, midrest) = T.splitAt relS rest
          (mid, post) = T.splitAt (relE - relS) midrest
          wrapped =
            el
              "span"
              [ ("class", roleClass (markRole mk))
              , ("data-tip", markTip mk)
              , ("tabindex", "0")
              ]
              (txt (if T.null mid then tokenFallback rest relS else mid))
       in txt pre <> wrapped <> go end ms post

    tokenFallback rest relS =
      let r = T.drop relS rest
       in T.takeWhile (not . isSpace) r
