{-# LANGUAGE ViewPatterns, TupleSections #-}
module Evaluator.Evaluate where

import Evaluator.Syntax

import Core.Syntax

import Renaming
import Utilities


var :: IdSupply -> InVar -> Chain
var ids in_x = Caboose (ids, Question in_x)

eval :: IdSupply -> In Term -> Chain
eval ids (rn, Var x)             = var ids (mkInVar rn x)
eval ids (rn, Value v)           = Caboose (ids, Answer (rn, v))
eval ids (rn, App e1 x2)         = Push (Apply (mkInVar rn x2)) `Wagon` eval ids (rn, e1)
eval ids (rn, PrimOp pop (x:xs)) = Push (PrimApply pop [] (map (mkInVar rn) xs)) `Wagon` var ids (mkInVar rn x)
eval ids (rn, Case x alts)       = Push (Scrutinise (rn, alts)) `Wagon` var ids (mkInVar rn x)
eval ids (rn, LetRec (unzip -> (xs, es)) e)
  = Allocate (map (mkInVar rn') xs `zip` map (rn',) es) `Wagon` eval ids' (rn', e)
  where (ids', rn', _xs') = renameBinders ids rn xs

resumeEvaluationContextFrame :: IdSupply -> EvaluationContextFrame -> In Value -> Chain
resumeEvaluationContextFrame ids (Apply in_x2)               in_v = apply      ids in_v in_x2
resumeEvaluationContextFrame ids (Scrutinise in_alts)        in_v = scrutinise ids in_v in_alts
resumeEvaluationContextFrame ids (PrimApply pop in_vs in_xs) in_v = primop     ids pop in_vs in_v in_xs
resumeEvaluationContextFrame ids (Update in_x)               in_v = update     ids in_x in_v

apply :: IdSupply -> In Value -> InVar -> Chain
apply ids (rn, Lambda x e_body) in_x2 = eval ids (insertRenaming x (outvar in_x2) rn, e_body)

scrutinise :: IdSupply -> In Value -> In [Alt] -> Chain
scrutinise ids (_,    Literal l)  (rn_alts, alts) = eval ids (head [(rn_alts, alt_e) | (LiteralAlt alt_l, alt_e) <- alts, alt_l == l])
scrutinise ids (rn_v, Data dc xs) (rn_alts, alts) = eval ids (head [(insertRenamings (alt_xs `zip` map (rename rn_v) xs) rn_alts, alt_e) | (DataAlt alt_dc alt_xs, alt_e) <- alts, alt_dc == dc])

primop :: IdSupply -> PrimOp -> [In Value] -> In Value -> [InVar] -> Chain
primop ids pop [(_, Literal l1)] (_, Literal l2) [] = Caboose (ids, Answer (emptyRenaming, Literal (f pop l1 l2)))
  where f pop = case pop of Add -> (+); Subtract -> (-); Multiply -> (*); Divide -> div
primop ids pop in_vs in_v (in_x:in_xs) = Push (PrimApply pop (in_vs ++ [in_v]) in_xs) `Wagon` var ids in_x

update :: IdSupply -> InVar -> In Value -> Chain
update ids in_x in_v = Allocate [(in_x, second Value in_v)] `Wagon` Caboose (ids, Answer in_v)
