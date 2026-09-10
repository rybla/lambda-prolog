-- | Wrap original source in nested semantic spans.
module Highlight
  ( highlight
  , parseHeader
  , Header (..)
  ) where

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Text (Text)
import Data.Text qualified as T

import Html (Html, el, raw, txt)
import LambdaProlog.Span (SrcPos (..), SrcSpan (..))
import LambdaProlog.Surface.Annotate
  ( Mark (..)
  , annotateSource
  , roleClass
  )
import LambdaProlog.Surface.Metadata
  ( Header (..)
  , parseHeader
  )

highlight :: FilePath -> Text -> Html
highlight file src =
  el "pre" [("class", "src")] (paint src (annotateSource file src))

paint :: Text -> [Mark] -> Html
paint src marks =
  foldMap (\(n, line) -> paintLine line n marks <> raw "\n") (zip [1 ..] (T.lines src))

paintLine :: Text -> Int -> [Mark] -> Html
paintLine line lineNo marks =
  let len = T.length line
      iv mk =
        let s = max 0 (posCol (spanStart (markSpan mk)) - 1)
            e0 = posCol (spanEnd (markSpan mk)) - 1
            e = min len (if e0 <= s then s + 1 else e0)
         in (s, e, mk)
      segs =
        [ (s, e, mk)
        | mk <- marks
        , posLine (spanStart (markSpan mk)) == lineNo
        , let (s, e, _) = iv mk
        , s < len && e > s && e <= len
        ]
   in paintSeg line 0 len segs

paintSeg :: Text -> Int -> Int -> [(Int, Int, Mark)] -> Html
paintSeg line from to segs
  | from >= to = mempty
  | otherwise =
      case covering of
        [] ->
          case later of
            [] -> txt (slice from to)
            (s, _, _) : _ ->
              txt (slice from s) <> paintSeg line s to segs
        (s, e, mk) : _ ->
          let inner = [(s', e', m) | (s', e', m) <- segs, s' >= s, e' <= e, (s', e', markSpan m) /= (s, e, markSpan mk)]
              wrapped =
                el
                  "span"
                  [ ("class", roleClass (markRole mk))
                  , ("data-tip", markTip mk)
                  , ("tabindex", "0")
                  ]
                  (paintSeg line s e inner)
           in (if s > from then txt (slice from s) else mempty)
                <> wrapped
                <> paintSeg line e to (filter (not . same (s, e, mk)) segs)
  where
    slice a b = T.take (b - a) (T.drop a line)
    covering =
      sortBy (comparing (negate . width) <> comparing start) $
        [(s, e, mk) | (s, e, mk) <- segs, s == from]
    later = sortBy (comparing start) [(s, e, mk) | (s, e, mk) <- segs, s > from]
    width (s, e, _) = e - s
    start (s, _, _) = s
    same (s, e, mk) (s', e', mk') =
      s == s' && e == e' && markSpan mk == markSpan mk' && markRole mk == markRole mk'
