-- | Elaboration: mixfix-resolved surface terms become kernel goals, clauses,
-- and a signature of kinds and typed constants.
module LambdaProlog.Surface.Elab
  ( Sig (..)
  , preludeSig
  , elabModule
  , elabQuery
  , elabQueryWithFrees
  , renderSTerm
  ) where

import Control.Monad (foldM)
import Control.Monad.State (State, evalState, get, put)
import Data.Char (isUpper)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text, uncons)
import Data.Text qualified as T

import LambdaProlog.Error (Error, mkError)
import LambdaProlog.Kernel.Goal
  ( Clause (..)
  , Goal (..)
  , Program
  , consultClause
  , emptyProgram
  , mapGoal
  )
import LambdaProlog.Kernel.Kind (Kind (..))
import LambdaProlog.Kernel.Term
  ( Head (..)
  , MetaId (..)
  , Term (..)
  , apps
  , con
  , intLit
  , lam
  , meta
  , shift
  , stringLit
  , var
  )
import LambdaProlog.Kernel.Type (Scheme (..), Type (..), tyArrs)
import LambdaProlog.Name (Interner, Name (..), intern, lookupName)
import LambdaProlog.Prelude
  ( Builtins (..)
  , prelude
  , tyList
  , tyO
  )
import LambdaProlog.Surface.Fixity (defaultOps, mixfixModule, mixfixTerm)
import LambdaProlog.Surface.Syntax

data Sig = Sig
  { sigInterner :: Interner
  , sigTyCons :: Map Name Kind
  , sigConsts :: Map Name Scheme
  }

preludeSig :: Sig
preludeSig =
  let b = prelude
      intern_ = bInterner b
      tyCons =
        Map.fromList
          [ (bO b, KType)
          , (bInt b, KType)
          , (bString b, KType)
          , (bList b, KArr KType KType)
          ]
      a = TyGen 0
      consts =
        Map.fromList
          [ (bTrue b, Scheme 0 tyO)
          , (bFail b, Scheme 0 tyO)
          , (bCut b, Scheme 0 tyO)
          , (bNil b, Scheme 1 (tyList a))
          , (bCons b, Scheme 1 (tyArrs [a, tyList a] (tyList a)))
          , (bEq b, Scheme 1 (tyArrs [a, a] tyO))
          , (bPi b, Scheme 1 (tyArrs [TyArr a tyO] tyO))
          , (bSigma b, Scheme 1 (tyArrs [TyArr a tyO] tyO))
          , (bNot b, Scheme 0 (TyArr tyO tyO))
          ]
   in Sig intern_ tyCons consts

data EEnv = EEnv
  { eeBound :: Map Text Term
  , eeNextId :: Int
  }

elabModule :: Module -> Either Error (Sig, Program)
elabModule m0 = do
  m <- mixfixModule defaultOps m0
  sg1 <- foldM elabDeclSig preludeSig (modDecls m)
  prog <- foldM (elabDeclClause sg1) emptyProgram (modDecls m)
  pure (sg1, prog)

elabQuery :: Sig -> STerm -> Either Error ([MetaId], Goal)
elabQuery sg t0 = do
  (mapping, g) <- elabQueryWithFrees sg t0
  pure (map snd mapping, g)

elabQueryWithFrees :: Sig -> STerm -> Either Error ([(Text, MetaId)], Goal)
elabQueryWithFrees sg t0 = do
  t <- mixfixTerm defaultOps (renameWildcards t0)
  let frees = freeVarsClause t
      mapping = zip frees (map MetaId [0 ..])
      env = EEnv (Map.fromList [(v, meta mid) | (v, mid) <- mapping]) (length frees)
  g <- elabGoal sg env t
  pure (mapping, g)

--------------------------------------------------------------------------------
-- Signature declarations
--------------------------------------------------------------------------------

elabDeclSig :: Sig -> Decl -> Either Error Sig
elabDeclSig sg d = case d of
  DKind ids k -> do
    kk <- elabKind k
    foldM (\s i -> addTyCon s i kk) sg ids
  DType ids ty -> do
    sch <- elabScheme sg ty
    foldM (\s i -> addConst s i sch) sg ids
  DLocal ids (Just ty) -> do
    sch <- elabScheme sg ty
    foldM (\s i -> addConst s i sch) sg ids
  DLocal ids Nothing ->
    foldM (\s i -> addConst s i (Scheme 1 (TyGen 0))) sg ids
  DExportDef ids (Just ty) -> elabDeclSig sg (DType ids ty)
  DExportDef ids Nothing ->
    foldM (\s i -> addConst s i (Scheme 0 tyO)) sg ids
  DUseOnly ids mty -> elabDeclSig sg (DExportDef ids mty)
  DClosed ids mty -> elabDeclSig sg (DLocal ids mty)
  DTypeAbbrev {} -> Right sg
  DFixity {} -> Right sg
  DLocalKind ids _ ->
    foldM (\s i -> addTyCon s i KType) sg ids
  DClause {} -> Right sg
  DQuery {} -> Right sg

addTyCon :: Sig -> Ident -> Kind -> Either Error Sig
addTyCon sg i k =
  let (n, intern') = intern (identName i) (sigInterner sg)
   in Right sg {sigInterner = intern', sigTyCons = Map.insert n k (sigTyCons sg)}

addConst :: Sig -> Ident -> Scheme -> Either Error Sig
addConst sg i sch =
  let (n, intern') = intern (identName i) (sigInterner sg)
   in Right sg {sigInterner = intern', sigConsts = Map.insert n sch (sigConsts sg)}

elabKind :: SKind -> Either Error Kind
elabKind (SKType _) = Right KType
elabKind (SKArr _ a b) = KArr <$> elabKind a <*> elabKind b

elabScheme :: Sig -> SType -> Either Error Scheme
elabScheme sg ty =
  let vs = typeVars ty
      ix = Map.fromList (zip vs [0 ..])
   in Scheme (length vs) <$> elabType sg ix ty

typeVars :: SType -> [Text]
typeVars = go []
  where
    go acc t = case t of
      STCon i
        | isVarName (identName i) && identName i `notElem` acc -> acc ++ [identName i]
        | otherwise -> acc
      STArr _ a b -> go (go acc a) b
      STApp _ a b -> go (go acc a) b
      STParen _ a -> go acc a

elabType :: Sig -> Map Text Int -> SType -> Either Error Type
elabType sg ix t = case t of
  STCon i
    | isVarName (identName i) ->
        case Map.lookup (identName i) ix of
          Just n -> Right (TyGen n)
          Nothing -> Left (mkError ("unbound type variable " <> identName i))
    | otherwise -> do
        n <- internTyCon sg i
        Right (TyCon n [])
  STArr _ a b -> TyArr <$> elabType sg ix a <*> elabType sg ix b
  STApp _ a b -> do
    ta <- elabType sg ix a
    tb <- elabType sg ix b
    case ta of
      TyCon n args -> Right (TyCon n (args ++ [tb]))
      _ -> Left (mkError "type constructor expected")
  STParen _ a -> elabType sg ix a

internTyCon :: Sig -> Ident -> Either Error Name
internTyCon sg i =
  let (n, _) = intern (identName i) (sigInterner sg)
   in Right n

--------------------------------------------------------------------------------
-- Clauses
--------------------------------------------------------------------------------

elabDeclClause :: Sig -> Program -> Decl -> Either Error Program
elabDeclClause sg prog d = case d of
  DClause t -> do
    c <- elabTopClause sg t
    Right (consultClause c prog)
  _ -> Right prog

elabTopClause :: Sig -> STerm -> Either Error Clause
elabTopClause sg t0 =
  let t = renameWildcards t0
      (hd, body) = splitNeck t
      frees = freeVarsClause t
      mapping = zip frees (map MetaId [0 ..])
      env = EEnv (Map.fromList [(v, meta mid) | (v, mid) <- mapping]) (length frees)
   in do
        (p, args) <- elabHead sg env hd
        g <- elabGoal sg env body
        pure (Clause p (map snd mapping) args g)

splitNeck :: STerm -> (STerm, STerm)
splitNeck t =
  case viewInfix ":-" t of
    Just (h, b) -> (h, b)
    Nothing -> (t, SId (Ident "true" (termSpan t)))

elabHead :: Sig -> EEnv -> STerm -> Either Error (Name, [Term])
elabHead sg env t = do
  let (h, args) = viewApps t
  case h of
    SId i
      | Just (TApp (HConst p) []) <- Map.lookup (identName i) (eeBound env) -> do
          as <- mapM (elabTerm sg env) args
          Right (p, as)
      | otherwise -> do
          p <- internConst sg i
          as <- mapM (elabTerm sg env) args
          Right (p, as)
    _ -> Left (mkError "clause head must be an applied constant")

--------------------------------------------------------------------------------
-- Goals and terms
--------------------------------------------------------------------------------

elabGoal :: Sig -> EEnv -> STerm -> Either Error Goal
elabGoal sg env t
  | Just (a, b) <- viewInfix "," t =
      GAnd <$> elabGoal sg env a <*> elabGoal sg env b
  | Just (a, b) <- viewInfix ";" t =
      GOr <$> elabGoal sg env a <*> elabGoal sg env b
  | Just (d, g) <- viewInfix "=>" t = do
      (cs, _) <- elabHyps sg env d
      GImpl cs <$> elabGoal sg env g
  | Just (a, b) <- viewInfix "=" t =
      GEq <$> elabTerm sg env a <*> elabTerm sg env b
  | Just (a, b) <- viewInfix "is" t =
      GIs <$> elabTerm sg env a <*> elabTerm sg env b
  | SCut _ <- t = Right GCut
  | SId i <- t, identName i == "true" = Right GTrue
  | SId i <- t, identName i == "fail" = Right GFail
  | SId i <- t, identName i == "!" = Right GCut
  | Just (bs, body) <- viewPi t = elabBinders GForall sg env bs body
  | Just (bs, body) <- viewSigma t = elabBinders GExists sg env bs body
  | SApp _ (SId i) g <- t, identName i == "not" =
      GNot <$> elabGoal sg env g
  | otherwise = do
      (h, args) <- pure (viewApps t)
      case h of
        SId i
          | Just tm <- Map.lookup (identName i) (eeBound env) ->
              case tm of
                TApp (HMeta m) [] -> do
                  as <- mapM (elabTerm sg env) args
                  Right (GFlex m as)
                TApp (HConst p) [] -> do
                  as <- mapM (elabTerm sg env) args
                  Right (GAtom p as)
                _ -> Left (mkError "not a goal")
          | otherwise -> do
              p <- internConst sg i
              as <- mapM (elabTerm sg env) args
              Right (GAtom p as)
        _ -> Left (mkError "not a goal")

peelLams :: STerm -> ([(Ident, Maybe SType)], STerm)
peelLams (SLam _ x ty b) =
  let (xs, r) = peelLams b
   in ((x, ty) : xs, r)
peelLams t = ([], t)

elabBinders ::
  (Type -> (Term -> Goal) -> Goal) ->
  Sig ->
  EEnv ->
  [(Ident, Maybe SType)] ->
  STerm ->
  Either Error Goal
elabBinders _ _ _ [] _ = Left (mkError "empty binder list")
elabBinders wrap sg env ((x, _) : xs) body = do
  let ph = Name (negate (eeNextId env + 1))
      env' =
        env
          { eeNextId = eeNextId env + 1
          , eeBound = Map.insert (identName x) (con ph) (eeBound env)
          }
  inner <- case xs of
    [] -> elabGoal sg env' body
    _ -> elabBinders wrap sg env' xs body
  pure $
    wrap tyO $ \e ->
      mapGoal (substConst ph e) inner

elabHyps :: Sig -> EEnv -> STerm -> Either Error ([Clause], Int)
elabHyps sg env t
  | Just (a, b) <- viewInfix "," t = do
      (cs1, next1) <- elabHyps sg env a
      (cs2, next2) <- elabHyps sg env {eeNextId = next1} b
      pure (cs1 ++ cs2, next2)
  | otherwise = do
      (c, next') <- elabHypClause sg env t
      pure ([c], next')

elabHypClause :: Sig -> EEnv -> STerm -> Either Error (Clause, Int)
elabHypClause sg env t0 = do
  let t = renameWildcards t0
      (hd, body) = splitNeck t
      allVars = freeVars t
      locals = [v | v <- allVars, Map.notMember v (eeBound env)]
      startId = eeNextId env
      clmids = map MetaId [startId .. startId + length locals - 1]
      mapping = zip locals clmids
      env' =
        env
          { eeBound =
              Map.fromList [(v, meta mid) | (v, mid) <- mapping]
                `Map.union` eeBound env
          , eeNextId = startId + length locals
          }
  (p, args) <- elabHead sg env' hd
  g <- elabGoal sg env' body
  pure (Clause p clmids args g, eeNextId env')

elabTerm :: Sig -> EEnv -> STerm -> Either Error Term
elabTerm sg env t = case t of
  SId i
    | Just tm <- Map.lookup (identName i) (eeBound env) -> Right tm
    | isVarName (identName i) ->
        Left (mkError ("unbound variable " <> identName i))
    | otherwise -> con <$> internConst sg i
  SInt _ n -> Right (intLit n)
  SString _ s -> Right (stringLit s)
  SCut _ -> con <$> internConst sg (Ident "!" (termSpan t))
  SLam _ x _ body -> do
    let env' =
          env
            { eeBound =
                Map.insert (identName x) (var 0) $
                  Map.map (shift 1 0) (eeBound env)
            }
    lam <$> elabTerm sg env' body
  SList _ es tl -> do
    es' <- mapM (elabTerm sg env) es
    tl' <- case tl of
      Nothing -> con <$> internConst sg (Ident "nil" (termSpan t))
      Just u -> elabTerm sg env u
    consN <- internConst sg (Ident "::" (termSpan t))
    Right (foldr (\x xs -> apps (con consN) [x, xs]) tl' es')
  SApp _ a b -> do
    fa <- elabTerm sg env a
    fb <- elabTerm sg env b
    Right (apps fa [fb])
  SSeq _ xs -> do
    ys <- mapM (elabTerm sg env) xs
    case ys of
      [] -> Left (mkError "empty term")
      z : zs -> Right (apps z zs)
  SParen _ a -> elabTerm sg env a
  SAnn _ a _ -> elabTerm sg env a

--------------------------------------------------------------------------------
-- Views and substitution
--------------------------------------------------------------------------------

viewInfix :: Text -> STerm -> Maybe (STerm, STerm)
viewInfix op (SApp _ (SApp _ (SId i) l) r)
  | identName i == op = Just (l, r)
viewInfix _ _ = Nothing

viewApps :: STerm -> (STerm, [STerm])
viewApps = go []
  where
    go acc (SApp _ f a) = go (a : acc) f
    go acc t = (t, acc)

-- | @pi x\\ G@, nested @pi x\\ y\\ G@, and ELPI-style @pi x y\\ G@.
viewPi :: STerm -> Maybe ([(Ident, Maybe SType)], STerm)
viewPi t = case viewApps t of
  (SId i, args) | identName i == "pi" -> viewNaryBinders args
  _ -> Nothing

viewSigma :: STerm -> Maybe ([(Ident, Maybe SType)], STerm)
viewSigma t = case viewApps t of
  (SId i, args) | identName i == "sigma" -> viewNaryBinders args
  _ -> Nothing

-- | Split @x y (z\\ G)@ into binders @[x,y,z]@ and body @G@. A lone
-- non-λ argument (@pi F@) is left to higher-order search.
viewNaryBinders :: [STerm] -> Maybe ([(Ident, Maybe SType)], STerm)
viewNaryBinders args =
  let (ids, rest) = span isBinderId args
      leading = [(i, Nothing) | SId i <- ids]
   in case rest of
        [fn@SLam {}] ->
          let (more, body) = peelLams fn
           in Just (leading ++ more, body)
        _ -> Nothing

isBinderId :: STerm -> Bool
isBinderId (SId _) = True
isBinderId _ = False

substConst :: Name -> Term -> Term -> Term
substConst n e (TLam t) = TLam (substConst n e t)
substConst n e (TApp h ts) =
  let ts' = map (substConst n e) ts
   in case h of
        HConst n' | n == n' -> apps e ts'
        _ -> TApp h ts'

internConst :: Sig -> Ident -> Either Error Name
internConst sg i =
  case lookupName (identName i) (sigInterner sg) of
    Just n -> Right n
    Nothing -> Left (mkError ("undeclared constant '" <> identName i <> "'"))

isVarName :: Text -> Bool
isVarName t = case uncons t of
  Just (c, _) -> isUpper c || c == '_'
  Nothing -> False

freeVars :: STerm -> [Text]
freeVars = go []
  where
    go bound t = case t of
      SId i
        | isVarName (identName i)
            && identName i `notElem` bound
            && identName i `notElem` ["_"] ->
            [identName i]
        | otherwise -> []
      SLam _ x _ b -> go (identName x : bound) b
      SApp _ a b -> nub (go bound a ++ go bound b)
      SSeq _ xs -> nub (concatMap (go bound) xs)
      SList _ es tl -> nub (concatMap (go bound) es ++ maybe [] (go bound) tl)
      SAnn _ a _ -> go bound a
      SParen _ a -> go bound a
      _ -> []

-- | Free variables of a top-level clause or query term.
-- Variables inside the assumption D of (D => G) are only considered free
-- in the outer clause if they also appear in G or in the enclosing context.
freeVarsClause :: STerm -> [Text]
freeVarsClause t =
  let (hd, body) = splitNeck t
      hVars = freeVars hd
   in nub (hVars ++ freeVarsGoal hVars body)

freeVarsGoal :: [Text] -> STerm -> [Text]
freeVarsGoal inScope = go []
  where
    go bound tm = case tm of
      _ | Just (d, g) <- viewInfix "=>" tm ->
          let gVars = go bound g
              dVars = go bound d
              shared = filter (\v -> v `elem` inScope || v `elem` gVars) dVars
           in nub (gVars ++ shared)
      SId i
        | isVarName (identName i)
            && identName i `notElem` bound
            && identName i `notElem` ["_"] ->
            [identName i]
        | otherwise -> []
      SLam _ x _ b -> go (identName x : bound) b
      SApp _ a b -> nub (go bound a ++ go bound b)
      SSeq _ xs -> nub (concatMap (go bound) xs)
      SList _ es tl -> nub (concatMap (go bound) es ++ maybe [] (go bound) tl)
      SAnn _ a _ -> go bound a
      SParen _ a -> go bound a
      _ -> []

nub :: (Eq a) => [a] -> [a]
nub [] = []
nub (x : xs) = x : nub (filter (/= x) xs)

-- | Each anonymous @_@ becomes a distinct logic variable.
renameWildcards :: STerm -> STerm
renameWildcards t = evalState (rw t) (0 :: Int)

rw :: STerm -> State Int STerm
rw t = case t of
  SId i
    | identName i == "_" -> do
        n <- get
        put (n + 1)
        pure (SId i {identName = "_W" <> packInt n})
    | otherwise -> pure t
  SSeq sp xs -> SSeq sp <$> mapM rw xs
  SApp sp a b -> SApp sp <$> rw a <*> rw b
  SLam sp x ty b -> SLam sp x ty <$> rw b
  SList sp es tl -> SList sp <$> mapM rw es <*> traverse rw tl
  SParen sp a -> SParen sp <$> rw a
  SAnn sp a ty -> SAnn sp <$> rw a <*> pure ty
  _ -> pure t

packInt :: Int -> Text
packInt n = T.pack (show n)

-- | Render surface term for informative error and query messages.
renderSTerm :: STerm -> Text
renderSTerm tm = case tm of
  SId i -> identName i
  SInt _ n -> T.pack (show n)
  SString _ s -> T.pack (show s)
  SCut _ -> "!"
  SLam _ x _ b -> identName x <> "\\ " <> renderSTerm b
  SApp _ (SApp _ (SId (Ident op _)) l) r
    | isSymOp op -> renderAtom l <> " " <> op <> " " <> renderAtom r
  SApp _ f a -> renderSTerm f <> " " <> renderAtom a
  SSeq _ xs -> T.unwords (map renderAtom xs)
  SList _ es tl ->
    "[" <> T.intercalate ", " (map renderSTerm es)
      <> (case tl of
            Nothing -> ""
            Just t -> " | " <> renderSTerm t)
      <> "]"
  SParen _ a -> "(" <> renderSTerm a <> ")"
  SAnn _ a _ -> renderSTerm a

isSymOp :: Text -> Bool
isSymOp op = op `elem` [":-", ",", ";", "=>", "=", "<", ">", "=<", ">=", "::", "+", "-", "*", "div", "mod", "^", "is"]

renderAtom :: STerm -> Text
renderAtom tm = case tm of
  SApp {} -> "(" <> renderSTerm tm <> ")"
  SLam {} -> "(" <> renderSTerm tm <> ")"
  _ -> renderSTerm tm
