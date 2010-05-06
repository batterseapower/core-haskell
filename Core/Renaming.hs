{-# LANGUAGE ViewPatterns #-}
module Core.Renaming (
    renameValue,
    renameTerm,
    renameAlt, renameAltCon, renameAlts,
  ) where

import Core.Syntax

import Renaming
import Utilities


type In a = a
type Out a = a

renameValue :: IdSupply -> Renaming -> In Value -> Out Value
renameValue ids rn v = case v of
    Lambda x e -> Lambda x' (renameTerm ids' rn' e)
      where (ids', rn', x') = renameBinder ids rn x
    Data dc xs -> Data dc (map (rename rn) xs)
    Literal l -> Literal l

renameTerm :: IdSupply -> Renaming -> In Term -> Out Term
renameTerm ids rn e = case e of
    Var x -> Var (safeRename "renameTerm" rn x)
    Value v -> Value (renameValue ids rn v)
    App e1 x2 -> App (renameTerm ids rn e1) (rename rn x2)
    PrimOp pop xs -> PrimOp pop (map (rename rn) xs)
    Case x alts -> Case (rename rn x) (renameAlts ids rn alts)
    LetRec (unzip -> (xs, es)) e -> LetRec (zipWith (\x' e -> (x', renameTerm ids' rn' e)) xs' es) (renameTerm ids' rn' e)
      where (ids', rn', xs') = renameBinders ids rn xs

renameAlt :: IdSupply -> Renaming -> In Alt -> Out Alt
renameAlt ids rn (alt_con, alt_e) = (alt_con', renameTerm ids' rn' alt_e)
  where (ids', rn', alt_con') = renameAltCon ids rn alt_con

renameAltCon :: IdSupply -> Renaming -> In AltCon -> (IdSupply, Renaming, Out AltCon)
renameAltCon ids rn_alt alt_con = case alt_con of
    LiteralAlt _          -> (ids, rn_alt, alt_con)
    DataAlt alt_dc alt_xs -> third3 (DataAlt alt_dc) $ renameBinders ids rn_alt alt_xs

renameAlts :: IdSupply -> Renaming -> In [Alt] -> Out [Alt]
renameAlts ids rn = map (renameAlt ids rn)
