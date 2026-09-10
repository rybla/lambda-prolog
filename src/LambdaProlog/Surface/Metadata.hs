-- | Module header comment metadata parsing.
module LambdaProlog.Surface.Metadata
  ( Header (..)
  , parseHeader
  , parseHeaderFields
  ) where

import Data.Char (isAlphaNum, isSpace)
import Data.Text (Text)
import Data.Text qualified as T

data Header = Header
  { hdrTitle :: Text
  , hdrTags :: [Text]
  , hdrSummary :: Text
  }
  deriving stock (Eq, Show)

-- | Parse the metadata header of a module into a structured 'Header'.
parseHeader :: Text -> Header
parseHeader src =
  let fields = parseHeaderFields src
      grab key =
        case [v | (k, v) <- fields, T.toLower k == T.toLower key] of
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

-- | Parse all metadata fields from module header comments.
--
-- A metadata field starts with a line containing a key followed by a colon
-- and the first part of the metadata value. If there are indented lines
-- following that line, their text is included in the metadata's value for that key.
parseHeaderFields :: Text -> [(Text, Text)]
parseHeaderFields src = go (takeWhile isHeaderLine (T.lines src))
  where
    isHeaderLine l =
      let s = T.stripStart l
       in not ("module " `T.isPrefixOf` s || "sig " `T.isPrefixOf` s)
            && (T.null s || "%" `T.isPrefixOf` s || "/*" `T.isPrefixOf` s || "*" `T.isPrefixOf` s)

    go [] = []
    go (l : ls) =
      case parseCommentLine l of
        Just (baseIndent, content)
          | Just (key, val0) <- parseFieldKey content ->
              let (contLines, restLs) = takeContinuation baseIndent ls
                  fullVal = T.unwords (filter (not . T.null) (val0 : contLines))
               in (key, fullVal) : go restLs
        _ -> go ls

    takeContinuation _ [] = ([], [])
    takeContinuation baseIndent (nxt : rest) =
      case parseCommentLine nxt of
        Just (indent, cont)
          | indent > baseIndent && not (T.null (T.strip cont)) ->
              let (more, remaining) = takeContinuation baseIndent rest
               in (T.strip cont : more, remaining)
        _ -> ([], nxt : rest)

parseCommentLine :: Text -> Maybe (Int, Text)
parseCommentLine l =
  let s = T.stripStart l
   in if "%" `T.isPrefixOf` s
        then
          let after = T.dropWhile (== '%') s
              spaces = T.takeWhile isSpace after
              content = T.dropWhile isSpace after
           in Just (indentWidth spaces, content)
        else if "/*" `T.isPrefixOf` s
          then
            let after0 = T.drop 2 s
                after = stripEndComment after0
                spaces = T.takeWhile isSpace after
                content = T.dropWhile isSpace after
             in Just (indentWidth spaces, content)
        else if "*" `T.isPrefixOf` s && not ("*/" `T.isPrefixOf` s)
          then
            let after0 = T.drop 1 s
                after = stripEndComment after0
                spaces = T.takeWhile isSpace after
                content = T.dropWhile isSpace after
             in Just (indentWidth spaces, content)
        else Nothing
  where
    stripEndComment t =
      let t' = T.stripEnd t
       in if "*/" `T.isSuffixOf` t'
            then T.dropEnd 2 t'
            else t

indentWidth :: Text -> Int
indentWidth = T.foldl' (\acc c -> if c == '\t' then acc + 4 - (acc `mod` 4) else acc + 1) 0

parseFieldKey :: Text -> Maybe (Text, Text)
parseFieldKey content =
  case T.break (== ':') content of
    (key, rest)
      | not (T.null key)
          && not (T.null rest)
          && T.all isKeyChar key ->
          Just (key, T.strip (T.drop 1 rest))
      | otherwise -> Nothing
  where
    isKeyChar c = isAlphaNum c || c == '_' || c == '-'
