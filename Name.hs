module Name (
    Name(name_string), name,
    freshName, freshNames
  ) where

import Utilities

import Data.Function
import Data.List
import Data.Ord


data Name = Name {
    name_string :: String,
    name_id :: Maybe Id
  }

instance Show Name where
    show = show . pPrint

instance Eq Name where
    (==) = (==) `on` name_key

instance Ord Name where
    compare = comparing name_key

instance Pretty Name where
    pPrintPrec level _ n = text (escape $ name_string n) <> maybe empty (\i -> char '_' <> text (show i)) (name_id n)
      where escape | level == haskellLevel = concatMap $ \c -> if c == '$' then "" else [c]
                   | otherwise             = id

name_key :: Name -> Either String Id
name_key n = maybe (Left $ name_string n) Right (name_id n)

name :: String -> Name
name s = Name s Nothing

freshName :: IdSupply -> String -> (IdSupply, Name)
freshName ids s = second (Name s . Just) $ stepIdSupply ids

freshNames :: IdSupply -> [String] -> (IdSupply, [Name])
freshNames = mapAccumL freshName
