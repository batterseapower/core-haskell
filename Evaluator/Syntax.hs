module Evaluator.Syntax where

import Core.Syntax

import Renaming
import Utilities

import Data.Function


type In a = (Renaming, a)
type Out a = a


-- | Special representation of (In Var) so we can use it as a key in a Map.
--
-- TODO: we don't actually compare by the invar (this is necessary because e.g. several
-- different invars could be renamed to the same outvar, and we want the evaluator to
-- be able to inline the corresponding bind!) so we could probably move the invar elsewhere.
data InVar = InVar { invar :: Var, outvar :: Out Var }

instance Eq InVar where
    (==) = (==) `on` outvar

instance Ord InVar where
    compare = compare `on` outvar

mkInVar :: Renaming -> Var -> InVar
mkInVar = curry toInVar

toInVar :: In Var -> InVar
toInVar (rn, x) = InVar x (safeRename "toInVar" rn x)

fromInVar :: InVar -> In Var
fromInVar (InVar x x') = (insertRenaming x x' emptyRenaming, x)


data Event = Push EvaluationContextFrame
           | Allocate [(InVar, In Term)]

data QA = Question InVar
        | Answer   (In Value)

type Chain = Train Event (IdSupply, QA)

data EvaluationContextFrame = Apply InVar
                            | Scrutinise (In [Alt])
                            | PrimApply PrimOp [In Value] [InVar]
                            | Update InVar
