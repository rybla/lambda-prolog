-- | Pretty-printers for kinds, types, and kernel terms.
module LambdaProlog.Kernel.Pretty
  ( PrintEnv (..)
  , mkPrintEnv
  , prettyKind
  , prettyType
  , prettyTerm
  , prettyHead
  , renderKind
  , renderType
  , renderTerm
  ) where

import Data.Char (chr, ord)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as T
import Prettyprinter
  ( Doc
  , comma
  , hsep
  , parens
  , pretty
  , punctuate
  , sep
  , (<+>)
  )

import LambdaProlog.Kernel.Kind (Kind (..))
import LambdaProlog.Kernel.Term (Head (..), Lit (..), MetaId (..), Term (..))
import LambdaProlog.Kernel.Type (Type (..))
import LambdaProlog.Name (Interner, Name, lookupName, nameText)
import LambdaProlog.Pretty (renderDocUnlined)

-- | Names needed to re-sugar lists and to print metas.
data PrintEnv = PrintEnv
  { peInterner :: Interner
  , peNil :: Maybe Name
  , peCons :: Maybe Name
  , peMetas :: IntMap Text
  }

mkPrintEnv :: Interner -> PrintEnv
mkPrintEnv intern =
  PrintEnv
    { peInterner = intern
    , peNil = lookupName "nil" intern
    , peCons = lookupName "::" intern
    , peMetas = IntMap.empty
    }

prettyKind :: Kind -> Doc ann
prettyKind = go False
  where
    go _ KType = pretty ("type" :: Text)
    go paren (KArr a b) =
      parenth paren (go True a <+> pretty ("->" :: Text) <+> go False b)

prettyType :: PrintEnv -> Type -> Doc ann
prettyType env = go (0 :: Int)
  where
    -- 0 = arrow (loosest), 1 = constructor application, 2 = atom
    go prec t = case t of
      TyArr a b ->
        parenth (prec > 0) (go 1 a <+> pretty ("->" :: Text) <+> go 0 b)
      TyCon n [] -> pretty (nameText (peInterner env) n)
      TyCon n args ->
        let hd = pretty (nameText (peInterner env) n)
            body = hsep (hd : map (go 2) args)
         in parenth (prec > 1) body
      TyGen i -> pretty (genName i)
      TyMeta i -> pretty ("?t" :: Text) <> pretty i

prettyHead :: PrintEnv -> [Text] -> Head -> Doc ann
prettyHead env ctx h = case h of
  HConst n -> pretty (nameText (peInterner env) n)
  HBound i
    | i >= 0 && i < length ctx -> pretty (ctx !! i)
    | otherwise -> pretty ("#" :: Text) <> pretty i
  HMeta (MetaId m) ->
    case IntMap.lookup m (peMetas env) of
      Just nm -> pretty nm
      Nothing -> pretty ("X" :: Text) <> pretty m
  HLit (LInt n) -> pretty n
  HLit (LString s) -> pretty (show s)

prettyTerm :: PrintEnv -> Term -> Doc ann
prettyTerm env = go [] False
  where
    go ctx paren t = case t of
      TLam _ ->
        let (names, body) = collectLams ctx t
            binders = hsep (map (\n -> pretty n <> pretty ("\\" :: Text)) names)
         in parenth paren (binders <+> go (reverse names ++ ctx) False body)
      TApp h ts ->
        case viewList env h ts of
          Just (elems, Nothing) ->
            pretty '[' <> sep (punctuate comma (map (go ctx False) elems)) <> pretty ']'
          Just (elems, Just tl) ->
            pretty '['
              <> sep (punctuate comma (map (go ctx False) elems))
              <+> pretty '|'
              <+> go ctx False tl
              <> pretty ']'
          Nothing ->
            case ts of
              [] -> prettyHead env ctx h
              _ ->
                parenth paren $
                  hsep (prettyHead env ctx h : map (go ctx True) ts)

    collectLams ctx t = collect ctx [] t
    collect ctx acc (TLam b) =
      let nm = freshName ctx acc
       in collect (nm : ctx) (nm : acc) b
    collect _ acc body = (reverse acc, body)

renderKind :: Kind -> Text
renderKind = renderDocUnlined . prettyKind

renderType :: PrintEnv -> Type -> Text
renderType env = renderDocUnlined . prettyType env

renderTerm :: PrintEnv -> Term -> Text
renderTerm env = renderDocUnlined . prettyTerm env

parenth :: Bool -> Doc ann -> Doc ann
parenth True = parens
parenth False = id

genName :: Int -> Text
genName i
  | i < 26 = T.singleton (chr (ord 'A' + i))
  | otherwise = T.singleton (chr (ord 'A' + (i `mod` 26))) <> T.pack (show (i `div` 26))

freshName :: [Text] -> [Text] -> Text
freshName ctx acc = go (0 :: Int)
  where
    used = ctx ++ acc
    go n =
      let cand = binderName n
       in if cand `elem` used then go (n + 1) else cand

binderName :: Int -> Text
binderName 0 = "x"
binderName 1 = "y"
binderName 2 = "z"
binderName n = "x" <> T.pack (show (n - 2))

-- | Recognize @nil@ / @::@ spines as lists.
viewList :: PrintEnv -> Head -> [Term] -> Maybe ([Term], Maybe Term)
viewList env h ts = do
  nilN <- peNil env
  consN <- peCons env
  go nilN consN h ts
  where
    go nilN _consN (HConst n) []
      | n == nilN = Just ([], Nothing)
    go nilN consN (HConst n) [x, rest]
      | n == consN =
          case rest of
            TApp h' ts' ->
              case go nilN consN h' ts' of
                Just (xs, tl) -> Just (x : xs, tl)
                Nothing -> Just ([x], Just rest)
            TLam _ -> Just ([x], Just rest)
    go _ _ _ _ = Nothing
