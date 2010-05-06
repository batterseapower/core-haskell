{-# LANGUAGE ViewPatterns #-}
module Evaluator.Renaming where

import Evaluator.Syntax

import Renaming
import Utilities

import Data.List


renameIn :: (IdSupply -> Renaming -> a -> a) -> IdSupply -> In a -> a
renameIn f ids (rn, x) = f ids rn x

renameInRenaming :: Renaming -> In a -> In a
renameInRenaming rn_by (rn, x) = (renameRenaming rn_by rn, x)

renameInVar :: Renaming -> InVar -> InVar
renameInVar rn in_x = InVar (invar in_x) (safeRename "renameInVar" rn (outvar in_x))

renameInVarBinder :: IdSupply -> Renaming -> InVar -> (IdSupply, Renaming, InVar)
renameInVarBinder ids rn in_x = (ids', rn', InVar (invar in_x) outvar')
  where (ids', rn', outvar') = renameBinder ids rn (outvar in_x)

renameInVarBinders :: IdSupply -> Renaming -> [InVar] -> (IdSupply, Renaming, [InVar])
renameInVarBinders ids rn xs = reassociate $ mapAccumL ((associate .) . uncurry renameInVarBinder) (ids, rn) xs
  where associate   (ids, rn, x)    = ((ids, rn), x)
        reassociate ((ids, rn), xs) = (ids, rn, xs)

renameQARenaming :: Renaming -> QA -> QA -- TODO: refactor QA as (In QA) and hence avoid this function?
renameQARenaming rn (Question in_x) = Question (renameInVar rn in_x)
renameQARenaming rn (Answer in_v)   = Answer (renameInRenaming rn in_v)
