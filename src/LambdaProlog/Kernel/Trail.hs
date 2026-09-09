-- | Mutable meta cells and an undo trail. Search and unification run in 'ST'
-- and snapshot the trail so failure can roll back instantiations, eigen
-- constants, and the current @pi@-level.
module LambdaProlog.Kernel.Trail
  ( Trail
  , MetaCell (..)
  , newTrail
  , mark
  , unwind
  , currentLevel
  , pushLevel
  , popLevel
  , allocMeta
  , freshMeta
  , freshMetaAt
  , readMeta
  , bindMeta
  , registerEigen
  , eigenLevel
  , isEigen
  , snapshotBinds
  , runTrail
  ) where

import Control.Monad.ST (ST, runST)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import Data.Text (Text)

import LambdaProlog.Kernel.Term (Level (..), MetaId (..), Term)
import LambdaProlog.Name (Name)

data MetaCell = MetaCell
  { mcLevel :: Level
  , mcBind :: Maybe Term
  , mcName :: Maybe Text
  }
  deriving stock (Eq, Show)

data Undo
  = UCells (IntMap MetaCell)
  | UEigens (Map Name Level)
  | ULevel Level
  | UNext Int

data Trail s = Trail
  { trCells :: STRef s (IntMap MetaCell)
  , trEigens :: STRef s (Map Name Level)
  , trLevel :: STRef s Level
  , trNext :: STRef s Int
  , trUndo :: STRef s [Undo]
  }

newTrail :: ST s (Trail s)
newTrail = do
  cells <- newSTRef IntMap.empty
  eigens <- newSTRef Map.empty
  lev <- newSTRef (Level 0)
  nxt <- newSTRef 0
  undo <- newSTRef []
  pure (Trail cells eigens lev nxt undo)

mark :: Trail s -> ST s Int
mark tr = length <$> readSTRef (trUndo tr)

unwind :: Trail s -> Int -> ST s ()
unwind tr m = do
  us <- readSTRef (trUndo tr)
  let (toApply, keep) = splitAt (length us - m) us
  mapM_ (applyUndo tr) toApply
  writeSTRef (trUndo tr) keep

applyUndo :: Trail s -> Undo -> ST s ()
applyUndo tr u = case u of
  UCells cs -> writeSTRef (trCells tr) cs
  UEigens es -> writeSTRef (trEigens tr) es
  ULevel l -> writeSTRef (trLevel tr) l
  UNext n -> writeSTRef (trNext tr) n

pushUndo :: Trail s -> Undo -> ST s ()
pushUndo tr u = do
  us <- readSTRef (trUndo tr)
  writeSTRef (trUndo tr) (u : us)

currentLevel :: Trail s -> ST s Level
currentLevel tr = readSTRef (trLevel tr)

pushLevel :: Trail s -> ST s Level
pushLevel tr = do
  l <- readSTRef (trLevel tr)
  pushUndo tr (ULevel l)
  let l' = l + 1
  writeSTRef (trLevel tr) l'
  pure l'

popLevel :: Trail s -> ST s ()
popLevel tr = do
  l <- readSTRef (trLevel tr)
  pushUndo tr (ULevel l)
  writeSTRef (trLevel tr) (l - 1)

allocMeta :: Trail s -> MetaId -> Level -> Maybe Text -> ST s ()
allocMeta tr (MetaId i) lev nm = do
  cs <- readSTRef (trCells tr)
  nxt <- readSTRef (trNext tr)
  pushUndo tr (UCells cs)
  pushUndo tr (UNext nxt)
  writeSTRef (trCells tr) (IntMap.insert i (MetaCell lev Nothing nm) cs)
  writeSTRef (trNext tr) (max nxt (i + 1))

freshMeta :: Trail s -> Maybe Text -> ST s MetaId
freshMeta tr nm = do
  lev <- currentLevel tr
  freshMetaAt tr lev nm

freshMetaAt :: Trail s -> Level -> Maybe Text -> ST s MetaId
freshMetaAt tr lev nm = do
  i <- readSTRef (trNext tr)
  allocMeta tr (MetaId i) lev nm
  pure (MetaId i)

readMeta :: Trail s -> MetaId -> ST s MetaCell
readMeta tr mid@(MetaId i) = do
  cs <- readSTRef (trCells tr)
  case IntMap.lookup i cs of
    Just c -> pure c
    Nothing -> do
      lev <- currentLevel tr
      allocMeta tr mid lev Nothing
      readMeta tr mid

bindMeta :: Trail s -> MetaId -> Term -> ST s ()
bindMeta tr (MetaId i) t = do
  cell <- readMeta tr (MetaId i)
  cs <- readSTRef (trCells tr)
  pushUndo tr (UCells cs)
  writeSTRef (trCells tr) (IntMap.insert i cell {mcBind = Just t} cs)

registerEigen :: Trail s -> Name -> ST s ()
registerEigen tr n = do
  es <- readSTRef (trEigens tr)
  lev <- currentLevel tr
  pushUndo tr (UEigens es)
  writeSTRef (trEigens tr) (Map.insert n lev es)

eigenLevel :: Trail s -> Name -> ST s (Maybe Level)
eigenLevel tr n = Map.lookup n <$> readSTRef (trEigens tr)

isEigen :: Trail s -> Name -> ST s Bool
isEigen tr n = Map.member n <$> readSTRef (trEigens tr)

-- | Instantiated metas only.
snapshotBinds :: Trail s -> ST s (IntMap Term)
snapshotBinds tr = do
  cs <- readSTRef (trCells tr)
  pure $
    IntMap.mapMaybe mcBind cs

runTrail :: (forall s. Trail s -> ST s a) -> a
runTrail k = runST (newTrail >>= k)
