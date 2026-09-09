-- | Interned identifiers. Constants, type constructors, and display names for
-- metas all live in one pool so pretty-printing is a table lookup.
module LambdaProlog.Name
  ( Name (..)
  , Interner
  , emptyInterner
  , intern
  , internMany
  , lookupName
  , nameText
  , nameTextUnchecked
  , internerSize
  ) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text, pack)

-- | Interned identifier. Equality is pointer equality on the intern table.
newtype Name = Name {nameId :: Int}
  deriving stock (Show)
  deriving newtype (Eq, Ord)

data Interner = Interner
  { internNext :: Int
  , internNames :: IntMap Text
  , internIds :: Map Text Name
  }

instance Show Interner where
  show i = "Interner{size=" ++ show (internNext i) ++ "}"

emptyInterner :: Interner
emptyInterner =
  Interner
    { internNext = 0
    , internNames = IntMap.empty
    , internIds = Map.empty
    }

intern :: Text -> Interner -> (Name, Interner)
intern txt env =
  case Map.lookup txt (internIds env) of
    Just n -> (n, env)
    Nothing ->
      let n = Name (internNext env)
          env' =
            Interner
              { internNext = internNext env + 1
              , internNames = IntMap.insert (nameId n) txt (internNames env)
              , internIds = Map.insert txt n (internIds env)
              }
       in (n, env')

internMany :: [Text] -> Interner -> ([Name], Interner)
internMany txts env = go txts env []
  where
    go [] e acc = (reverse acc, e)
    go (t : ts) e acc =
      let (n, e') = intern t e
       in go ts e' (n : acc)

lookupName :: Text -> Interner -> Maybe Name
lookupName txt env = Map.lookup txt (internIds env)

-- | Inverse of 'intern'. Missing names (should not happen for interned
-- values) render as @#<id>@.
nameText :: Interner -> Name -> Text
nameText env (Name i) =
  case IntMap.lookup i (internNames env) of
    Just t -> t
    Nothing -> nameTextUnchecked (Name i)

nameTextUnchecked :: Name -> Text
nameTextUnchecked (Name i) = "#" <> pack (show i)

internerSize :: Interner -> Int
internerSize = internNext
