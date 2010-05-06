{-# LANGUAGE ViewPatterns, PatternGuards #-}
module Main (main) where

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Evaluate
import Evaluator.Renaming
import Evaluator.Syntax

import Name
import Renaming
import Utilities

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe


type PureHeap = M.Map InVar (In Term)
data Heap = Heap PureHeap IdSupply

type EvaluationContext = [EvaluationContextFrame]


evaluate :: Term -> (Heap, EvaluationContext, QA)
evaluate e = f (first3 (flip Heap ids2) $ initialiseTerm ids1 (mkIdentityRenaming $ S.toList $ termFreeVars e, e))
  where (ids1, ids2) = splitIdSupply reduceIdSupply
        f (Heap h ids, k, qa) = case qa of Answer   in_v | (kf:k)    <- k               -> g h k (resumeEvaluationContextFrame ids kf in_v)
                                           Question in_x | Just in_e <- M.lookup in_x h -> g (M.delete in_x h) (Update in_x : k) (eval ids in_e)
                                           _ -> (Heap h ids, k, qa)

        g h k chain = f (followChain h k chain)

initialiseTerm :: IdSupply -> In Term -> (PureHeap, EvaluationContext, QA)
initialiseTerm ids e = case followChain M.empty [] (eval ids e) of (Heap h _, k, qa) -> (h, k, qa)

followChain :: PureHeap -> EvaluationContext -> Chain -> (Heap, EvaluationContext, QA)
followChain h k (Caboose (ids, qa))             = (Heap h ids, k, qa)
followChain h k (Wagon (Allocate in_xes) chain) = followChain (h `M.union` M.fromList in_xes) k chain
followChain h k (Wagon (Push kf)         chain) = followChain h (kf:k) chain


residualiseAll :: Heap -> EvaluationContext -> QA -> Out Term
residualiseAll heap k qa = residualiseHeap heap (\ids -> residualiseEvaluationContext ids k (residualiseQA ids qa))

residualiseQA :: IdSupply -> QA -> Out Term
residualiseQA _   (Question in_x) = Var (outvar in_x)
residualiseQA ids (Answer in_v)   = Value (renameIn renameValue ids in_v)

residualiseHeap :: Heap -> (IdSupply -> ([(Out Var, Out Term)], Out Term)) -> Out Term
residualiseHeap (Heap h ids) (($ ids) -> (floats, e)) = letRec ([(outvar in_x, renameIn renameTerm ids in_e) | (in_x, in_e) <- M.toList h] ++ floats) e

residualiseEvaluationContext :: IdSupply -> [EvaluationContextFrame] -> Out Term -> ([(Out Var, Out Term)], Out Term)
residualiseEvaluationContext _   []     e = ([], e)
residualiseEvaluationContext ids (kf:k) (residualiseEvaluationContextFrame ids kf -> (floats, e)) = first (floats ++) $ residualiseEvaluationContext ids k e

residualiseEvaluationContextFrame :: IdSupply -> EvaluationContextFrame -> Out Term -> ([(Out Var, Out Term)], Out Term)
residualiseEvaluationContextFrame _   (Apply in_x2)               e1 = ([], App e1 (outvar in_x2))
residualiseEvaluationContextFrame ids (Scrutinise in_alts)        e  = (maybeToList mb_float, Case x' (renameIn renameAlts ids' in_alts))
  where (ids', mb_float, x') = freshFloatVar ids "scrut" e
residualiseEvaluationContextFrame ids (PrimApply pop in_vs in_xs) e  = (floats, PrimOp pop (ys' ++ map outvar in_xs))
  where (ids', floats, ys') = freshFloatVars ids "arg" (map (Value . renameIn renameValue ids') in_vs ++ [e])
residualiseEvaluationContextFrame _   (Update in_x)               e  = ([(x', e)], Var x')
  where x' = outvar in_x


main :: IO ()
main = do
    putStrLn "Input:"
    putStrLn $ pPrintRender e
    
    let e' = uncurry3 residualiseAll $ evaluate e
    putStrLn "Output:"
    putStrLn $ pPrintRender e'
  where
    lit = Value . Literal
    nilDataCon = "[]"
    nil = Value (Data nilDataCon [])
    consDataCon = "(:)"
    cons x xs = Value (Data consDataCon [x, xs])
    
    list s xs = uncurry letRec $ foldr (\(hd, i) (floats, e) -> let tl = name (s ++ show i) in ((tl, e) : floats, cons hd tl)) ([], nil) (xs `zip` [0..])
    
    trueDataCon = "True"
    true = Value (Data trueDataCon [])
    falseDataCon = "False"
    false = Value (Data falseDataCon [])
    
    nothingDataCon = "Nothing"
    nothing = Value (Data nothingDataCon [])
    justDataCon = "Just"
    just x = Value (Data justDataCon [x])
    
    if_ x et ef = Case x [(DataAlt trueDataCon [], et), (DataAlt falseDataCon [], ef)]
    
    {-
    -- Simple beta-reduction
    (rn, [cons_wrap, y, ys]) = freshBinders emptyRenaming ["cons_wrap", "y", "ys"]
    e = LetRec [(cons_wrap, Value $ Lambda y $ Value $ Lambda ys $ Value (Data consDataCon [y, ys]))] $
        (Case (list [Value (Literal 1)]) [(DataAlt consDataCon [y, ys], Var y)])
    -}

    {-
    -- Case-of-case mediated by an update frame: a bit tricky, because we need to do a linearity check upon residualisation
    [unknown, x, y] = map name ["unknown", "x", "y"]
    e = Value $ Lambda unknown $ LetRec [(x, Case unknown [(DataAlt nilDataCon [], nil)]),
                                         (y, Case x       [(DataAlt nilDataCon [], lit 10)])] $
                                 Var y
    -}
    
    {-
    -- Checks that we are able to gain information through case scrutinisation
    [unknown, x] = map name ["unknown", "x"]
    e = Value $ Lambda unknown $ Case unknown [(DataAlt justDataCon [x], Case unknown [(DataAlt justDataCon [x], Var x)])]
    -}
    
    {-
    -- A more challenging case where we gain information by scrutinisation
    [unknown1, unknown2, x] = map name ["unknown1", "unknown2", "x"]
    e = Value $ Lambda unknown1 $ Value (Lambda unknown2 (Case unknown1 [
                                                             (DataAlt justDataCon [x], Case unknown2 [(DataAlt justDataCon [x], Var x)])])) `App` unknown1
    -}
    
    {-
    -- Primarily a test of the correctness of the renamer
    (rn, [cons_wrap, eat, y, ys, x, xs, zs]) = freshBinders emptyRenaming ["cons_wrap", "eat", "y", "ys", "x", "xs", "zs"] -- y_u17, zs_u17
    e = LetRec [(cons_wrap, Value $ Lambda y $ Value $ Lambda ys $ Value (Data consDataCon [y, ys])),
                (eat, Value $ Lambda zs $ Case (Var zs) [(DataAlt consDataCon [x, xs], Value (PrimOp Add []) `App` Var x `App` Case (Var xs) [(DataAlt consDataCon [x, xs], Var x)])])] $
        (Var eat `App` list [Value (Literal 1), Value (Literal 2)])
    -}
    
    {-
    -- Tests that we gain information from cases and that our "cheapification" is reasonably good
    [sum, xs, y, ys, ys', one, two, three] = map name ["sum", "xs", "y", "ys", "ys'", "one", "two", "three"]
    e = LetRec [(sum, Value $ Lambda xs $
                          Case xs [(DataAlt nilDataCon  [],
                                      lit 0),
                                   (DataAlt consDataCon [y, ys],
                                      LetRec [(ys', Var sum `App` ys)] $
                                      PrimOp Add [y, ys'])]),
                (one, lit 1), (two, lit 2), (three, lit 3)] $
        (Value $ Lambda y $ Case y [(LiteralAlt 0, LetRec [(ys, list "list" [y, one, two, three])] $
                                                      Var sum `App` ys)])
    -}
    
    {-
    -- Tests recursive functions and residualisation
    [sum, xs, y, ys, ys', one, two, three] = map name ["sum", "xs", "y", "ys", "ys'", "one", "two", "three"]
    e = LetRec [(sum, Value $ Lambda xs $
                          Case xs [(DataAlt nilDataCon  [],
                                      lit 0),
                                   (DataAlt consDataCon [y, ys],
                                      LetRec [(ys', Var sum `App` ys)] $
                                      PrimOp Add [y, ys'])])] $
        (Value $ Lambda y $ LetRec [(one, lit 1), (two, lit 2), (three, lit 3),
                                    (ys, list "list" [y, one, two, three]] $
                            Var sum `App` ys)
    -}
    
    {-
    -- Tests that we pull down outer continuation frames into case branches
    (_rn, [cons_wrap, y, ys]) = freshBinders emptyRenaming ["cons_wrap", "y", "ys"]
    e = LetRec [(cons_wrap, Value $ Lambda y $ Value $ Lambda ys $ Value (Data consDataCon [y, ys]))] $
        (Value $ Lambda y $ Value (PrimOp Add []) `App` Case (Var y) [(LiteralAlt 1, Var y),
                                                                      (LiteralAlt 2, Value (Literal 1))] `App` Value (Literal 3))
    -}
    
    {-
    -- Tests whether we can do tupling (challenging?)
    [sum, length, average, a, b, v, vs, w, ws, x, xs, y, z, ys, zs] = map name ["sum", "length", "average", "a", "b", "v", "vs", "w", "ws", "x" ,"xs", "y", "z", "ys", "zs"]
    e = LetRec [(sum, Value $ Lambda xs $
                          Case xs [(DataAlt nilDataCon  [],
                                      lit 0),
                                   (DataAlt consDataCon [y, ys],
                                      LetRec [(zs, Var sum `App` ys)] $
                                      PrimOp Add [y, zs])]),
                (length, Value $ Lambda xs $
                              Case xs [(DataAlt nilDataCon  [],
                                          lit 0),
                                       (DataAlt consDataCon [w, ws],
                                          LetRec [(v, lit 1),
                                                  (vs, Var length `App` ws)] $
                                          PrimOp Add [v, vs])]),
                (average, Value $ Lambda xs $ LetRec [(a, Var sum `App` xs),
                                                      (b, Var length `App` xs)] $
                                              PrimOp Divide [a, b])] $
        (Value $ Lambda ys $ Var average `App` ys)
    -}
    
    {--}
    -- Tests simple function specialisation: map (1+)
    [mymap, f, xs, y, ys, z, zs] = map name ["map", "f", "xs", "y", "ys", "z", "zs"]
    e = LetRec [(mymap, Value $ Lambda f $ Value $ Lambda xs $
                          Case xs [(DataAlt nilDataCon  [],
                                      nil),
                                   (DataAlt consDataCon [y, ys],
                                      LetRec [(z, Var f `App` y),
                                              (zs, Var mymap `App` f `App` ys)] $
                                      cons z zs)]),
                (f, Value $ Lambda y $ LetRec [(z, Value (Literal 1))] $
                                       PrimOp Add [z, y])] $
        (Value $ Lambda ys $ Var mymap `App` f `App` ys)
    {--}
    
    {-
    (_rn, [cons_wrap, map, f, xs, y, ys, z, zs]) = freshBinders emptyRenaming ["cons_wrap", "map", "f", "xs", "y", "ys", "z", "zs"]
    e = LetRec [(cons_wrap, Value $ Lambda y $ Value $ Lambda ys $ Value (Data consDataCon [y, ys])),
                (map, Value $ Lambda f $ Value $ Lambda xs $
                          Case (Var xs) [(DataAlt nilDataCon  [],
                                            Value (Data nilDataCon [])),
                                         (DataAlt consDataCon [z, zs],
                                            Var cons_wrap `App` (Var f `App` Var z) `App` (Var map `App` Var f `App` Var zs))])] $
        (Value $ Lambda ys $ Var map `App` (Value $ Lambda y $ Value (PrimOp Add [Literal 1]) `App` Var y) `App` (Var map `App` (Value $ Lambda y $ Value (PrimOp Subtract [Literal 1]) `App` Var y) `App` Var ys))
    -}
    
    {-
    -- This example should NOT move expensive inside the z binding during supercompilation, but ideally
    -- it should float it up so that we can inline the primop application into both sides of the case
    [expensive, unk_f, unk_w, x, y, z] = map name ["expensive", "unk_f", "unk_w", "x", "y", "z"]
    e = Value $ Lambda unk_f $ Value $ Lambda unk_w $
          LetRec [(y, LetRec [(x, lit 2),
                              (expensive, Var unk_f `App` x)] $
                      Case unk_w [(DataAlt trueDataCon [], Value (Literal 1)),
                                  (DataAlt falseDataCon [], Var expensive)]),
                  (x, lit 10)] $
          Value (Lambda z $ PrimOp Add [y, x])
    -}
    
    {-
    -- Tests you can handle letrecs nicely
    [one, ones, x, xs, y, ys] = map name ["one", "ones", "x", "xs", "y", "ys"]
    e = LetRec [(one, lit 1),
                (ones, cons one ones)] $
        Case ones [(DataAlt consDataCon [x, xs], Case xs [(DataAlt consDataCon [y, ys], PrimOp Add [x, y])])]
    -}
    
    {-
    -- Tests that your termination criteria works
    [reverse, reverse_worker, xs, acc, acc', z, zs] = map name ["reverse", "reverse_worker", "xs", "acc", "acc'", "z", "zs"]
    e = LetRec [(reverse_worker, Value $ Lambda xs $ Value $ Lambda acc $
                                    Case xs [(DataAlt nilDataCon [],
                                                Var acc),
                                             (DataAlt consDataCon [z, zs],
                                                LetRec [(acc', cons z acc)] $
                                                Var reverse_worker `App` zs `App` acc')]),
                (zs, nil),
                (reverse, Value $ Lambda xs $ Var reverse_worker `App` xs `App` zs)] $
        (Var reverse)
    -}
