module Evaluator.FreeVars (
    renamingFreeVars, renamingFreeInVars,
    inFreeVars, inFreeInVars,
    qaFreeVars, evaluationContextFrameFreeVars
  ) where

import Evaluator.Syntax

import Core.FreeVars
import Core.Syntax

import Renaming

import qualified Data.Set as S


type FreeInVars = S.Set InVar

renamingFreeVars :: Renaming -> FreeVars -> FreeVars
renamingFreeVars rn fvs = S.map (rename rn) fvs

renamingFreeInVars :: Renaming -> FreeVars -> FreeInVars
renamingFreeInVars rn fvs = S.map (mkInVar rn) fvs

inFreeVars :: (a -> FreeVars) -> In a -> FreeVars
inFreeVars thing_fvs (rn, thing) = renamingFreeVars rn (thing_fvs thing)

inFreeInVars :: (a -> FreeVars) -> In a -> FreeInVars
inFreeInVars thing_fvs (rn, thing) = renamingFreeInVars rn (thing_fvs thing)

qaFreeVars :: QA -> FreeVars
qaFreeVars (Question in_x) = S.singleton (outvar in_x)
qaFreeVars (Answer in_v)   = inFreeVars valueFreeVars in_v

evaluationContextFrameFreeVars :: EvaluationContextFrame -> (S.Set Var, FreeVars)
evaluationContextFrameFreeVars kf = case kf of
    Apply in_x              -> (S.empty, S.singleton (outvar in_x))
    Scrutinise in_alts      -> (S.empty, inFreeVars altsFreeVars in_alts)
    PrimApply _ in_vs in_xs -> (S.empty, S.unions (map (inFreeVars valueFreeVars) in_vs) `S.union` S.fromList (map outvar in_xs))
    Update in_x             -> (S.singleton (outvar in_x), S.empty)
