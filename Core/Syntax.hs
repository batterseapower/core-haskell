{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Core.Syntax where

import Name
import Utilities

import Data.List
import Data.Maybe


type Var = Name

type DataCon = String

data PrimOp = Add | Subtract | Multiply | Divide
            deriving (Eq, Show)

data AltCon = DataAlt DataCon [Var] | LiteralAlt Literal
            deriving (Eq, Show)

type Literal = Int

data Term = Var Var | Value Value | App Term Var | PrimOp PrimOp [Var] | Case Var [Alt] | LetRec [(Var, Term)] Term
          deriving (Eq, Show)

type Alt = (AltCon, Term)

data Value = Lambda Var Term | Data DataCon [Var] | Literal Literal
           deriving (Eq, Show)

instance Pretty PrimOp where
    pPrint Add      = text "(+)"
    pPrint Subtract = text "(-)"
    pPrint Multiply = text "(*)"
    pPrint Divide   = text "(/)"

instance Pretty AltCon where
    pPrintPrec level prec altcon = case altcon of
        DataAlt dc xs -> prettyParen (prec >= appPrec) $ text dc <+> hsep (map (pPrintPrec level appPrec) xs)
        LiteralAlt l -> int l

instance Pretty Term where
    pPrintPrec level prec e = case e of
        LetRec xes e  -> pPrintPrecLetRec level prec xes e
        Var x         -> pPrintPrec level prec x
        Value v       -> pPrintPrec level prec v
        App e1 x2     -> pPrintPrecApp level prec e1 x2
        PrimOp pop xs -> pPrintPrecPrimOp level prec pop xs
        Case x alts  | level == haskellLevel, null alts -> text "undefined"
                     | otherwise                        -> pPrintPrecCase level prec x alts

pPrintPrecApp :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> b -> Doc
pPrintPrecApp level prec e1 e2 = prettyParen (prec >= appPrec) $ pPrintPrec level opPrec e1 <+> pPrintPrec level appPrec e2

pPrintPrecPrimOp :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> [b] -> Doc
pPrintPrecPrimOp level prec pop xs = pPrintPrecApps level prec pop xs

pPrintPrecCase :: (Pretty a, Pretty b, Pretty c) => PrettyLevel -> Rational -> a -> [(b, c)] -> Doc
pPrintPrecCase level prec e alts = prettyParen (prec > noPrec) $ hang (text "case" <+> pPrintPrec level noPrec e <+> text "of") 2 $ vcat (map (pPrintPrecAlt level noPrec) alts)

pPrintPrecAlt :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> (a, b) -> Doc
pPrintPrecAlt level _ (alt_con, alt_e) = hang (pPrintPrec level noPrec alt_con <+> text "->") 2 (pPrintPrec level noPrec alt_e)

pPrintPrecLetRec :: (Pretty a, Pretty b, Pretty c) => PrettyLevel -> Rational -> [(a, b)] -> c -> Doc
pPrintPrecLetRec level prec xes e
  | [] <- xes = pPrintPrec level prec e
  | otherwise = prettyParen (prec > noPrec) $ hang (if level == haskellLevel then text "let" else text "letrec") 2 (vcat [pPrintPrec level noPrec x <+> text "=" <+> pPrintPrec level noPrec e | (x, e) <- xes]) $$ text "in" <+> pPrintPrec level noPrec e

instance Pretty Value where
    pPrintPrec level prec v = case v of
        Lambda x e    -> pPrintPrecLam level prec (x:xs) e'
          where (xs, e') = collectLambdas e
        Data dc xs    -> pPrintPrecApps level prec (PrettyFunction $ \_ _ -> text dc) xs
        Literal l     -> int l

pPrintPrecLam :: Pretty a => PrettyLevel -> Rational -> [Var] -> a -> Doc
pPrintPrecLam level prec xs e = prettyParen (prec > noPrec) $ text "\\" <> hsep [pPrintPrec level appPrec y | y <- xs] <+> text "->" <+> pPrintPrec level noPrec e

pPrintPrecApps :: (Pretty a, Pretty b) => PrettyLevel -> Rational -> a -> [b] -> Doc
pPrintPrecApps level prec e1 es2 = prettyParen (not (null es2) && prec >= appPrec) $ pPrintPrec level opPrec e1 <+> hsep (map (pPrintPrec level appPrec) es2)


isVar :: Term -> Bool
isVar (Var _) = True
isVar _       = False

termVar_maybe :: Term -> Maybe Var
termVar_maybe (Var x) = Just x
termVar_maybe _       = Nothing

termValue_maybe :: Term -> Maybe Value
termValue_maybe (Value v) = Just v
termValue_maybe _         = Nothing

letRec :: [(Var, Term)] -> Term -> Term
letRec []  e = e
letRec xes e = LetRec xes e

lambdas :: [Var] -> Term -> Term
lambdas = flip $ foldr ((Value .) . Lambda)

apps :: Term -> [Var] -> Term
apps = foldl App

collectLambdas :: Term -> ([Var], Term)
collectLambdas (Value (Lambda x e)) = first (x:) $ collectLambdas e
collectLambdas e                    = ([], e)

freshFloatVar :: IdSupply -> String -> Term -> (IdSupply, Maybe (Name, Term), Name)
freshFloatVar ids s (Var x) = (ids,  Nothing,     x)
freshFloatVar ids s e       = (ids', Just (y, e), y)
  where (ids', y) = freshName ids s

freshFloatVars :: IdSupply -> String -> [Term] -> (IdSupply, [(Name, Term)], [Name])
freshFloatVars ids s es = reassociate $ mapAccumL (\ids -> associate . freshFloatVar ids s) ids es
  where reassociate (ids, unzip -> (mb_floats, xs)) = (ids, catMaybes mb_floats, xs)
        associate (ids, mb_float, x) = (ids, (mb_float, x))