module Core.FreeVars (
    FreeVars,
    termFreeVars, altConFreeVars, altFreeVars, altsFreeVars, valueFreeVars
  ) where

import Core.Syntax

import qualified Data.Set as S


type FreeVars = S.Set Var

deleteList :: Ord a => [a] -> S.Set a -> S.Set a
deleteList = flip $ foldr S.delete

termFreeVars :: Term -> FreeVars
termFreeVars (Var x)        = S.singleton x
termFreeVars (Value v)      = valueFreeVars v
termFreeVars (App e x)      = S.insert x $ termFreeVars e
termFreeVars (PrimOp _ xs)  = S.fromList xs
termFreeVars (Case x alts)  = S.insert x $ altsFreeVars alts
termFreeVars (LetRec xes e) = deleteList xs $ S.unions (map termFreeVars es) `S.union` termFreeVars e
  where (xs, es) = unzip xes

altConFreeVars :: AltCon -> FreeVars -> FreeVars
altConFreeVars (DataAlt _ xs) = deleteList xs
altConFreeVars (LiteralAlt _) = id

altFreeVars :: Alt -> FreeVars
altFreeVars (altcon, e) = altConFreeVars altcon $ termFreeVars e

altsFreeVars :: [Alt] -> FreeVars
altsFreeVars = S.unions . map altFreeVars

valueFreeVars :: Value -> FreeVars
valueFreeVars (Lambda x e) = S.delete x $ termFreeVars e
valueFreeVars (Data _ xs)  = S.fromList xs
valueFreeVars (Literal _)  = S.empty
