{-# LANGUAGE TupleSections, PatternGuards #-}
module Utilities (
    module IdSupply,
    module Utilities,
    
    module Control.Arrow,
    module Control.Exception,
    module Control.Monad,
    
    module Debug.Trace,
    
    module Text.PrettyPrint.HughesPJClass
  ) where

import IdSupply

import Control.Arrow (first, second, (***), (&&&))
import Control.Exception (assert)
import Control.Monad

import qualified Data.Set as S

import Debug.Trace

import Text.PrettyPrint.HughesPJClass hiding (render)

import System.IO.Unsafe (unsafePerformIO)


instance Pretty a => Pretty (S.Set a) where
    pPrint xs = char '{' <> hsep (punctuate (char ',') (map pPrint $ S.toList xs)) <> char '}'


{-# NOINLINE reduceIdSupply #-}
reduceIdSupply :: IdSupply
reduceIdSupply = unsafePerformIO $ initIdSupply 'u'

{-# NOINLINE normaliseIdSupply #-}
normaliseIdSupply :: IdSupply
normaliseIdSupply = unsafePerformIO $ initIdSupply 'n'

stepIdSupply :: IdSupply -> (IdSupply, Id)
stepIdSupply = second idFromSupply . splitIdSupply


data Train a b = Wagon a (Train a b)
               | Caboose b


appPrec, opPrec, noPrec :: Rational
appPrec = 2    -- Argument of a function application
opPrec  = 1    -- Argument of an infix operator
noPrec  = 0    -- Others

normalLevel, haskellLevel :: PrettyLevel
normalLevel = PrettyLevel 0
haskellLevel = PrettyLevel 1


angles, coangles :: Doc -> Doc
angles d = char '<' <> d <> char '>'
coangles d = char '>' <> d <> char '<'


pPrintPrec' :: Pretty a => a -> PrettyLevel -> Rational -> Doc
pPrintPrec' x level prec = pPrintPrec level prec x

-- NB: this render function is exported instead of the one from the library
render :: Doc -> String
render = renderStyle (style { lineLength = 120 })

pPrintRender :: Pretty a => a -> String
pPrintRender = render . pPrint


traceRender :: Pretty a => a -> b -> b
traceRender x = trace (pPrintRender x)


removeOnes :: [a] -> [[a]]
removeOnes [] = []
removeOnes (x:xs) = xs : map (x:) (removeOnes xs)


instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k, Pretty l,
          Pretty m, Pretty n, Pretty o) => Pretty (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k, pPrint l,
                     pPrint m, pPrint n, pPrint o]

pPrintTuple :: [Doc] -> Doc
pPrintTuple ds = parens $ fsep $ punctuate comma ds


newtype PrettyFunction = PrettyFunction (PrettyLevel -> Rational -> Doc)

instance Pretty PrettyFunction where
    pPrintPrec level prec (PrettyFunction f) = f level prec

asPrettyFunction :: Pretty a => a -> PrettyFunction
asPrettyFunction = PrettyFunction . pPrintPrec'


fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

first3 :: (a -> d) -> (a, b, c) -> (d, b, c)
first3 f (a, b, c) = (f a, b, c)

second3 :: (b -> d) -> (a, b, c) -> (a, d, c)
second3 f (a, b, c) = (a, f b, c)

third3 :: (c -> d) -> (a, b, c) -> (a, b, d)
third3 f (a, b, c) = (a, b, f c)

second4 :: (b -> e) -> (a, b, c, d) -> (a, e, c, d)
second4 f (a, b, c, d) = (a, f b, c, d)

third4 :: (c -> e) -> (a, b, c, d) -> (a, b, e, d)
third4 f (a, b, c, d) = (a, b, f c, d)

secondM :: Monad m => (b -> m c) -> (a, b) -> m (a, c)
secondM f (a, b) = liftM (a,) $ f b


uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c


splitBy :: [b] -> [a] -> ([a], [a])
splitBy []     xs     = ([], xs)
splitBy (_:ys) (x:xs) = first (x:) $ splitBy ys xs

splitManyBy :: [[b]] -> [a] -> [[a]]
splitManyBy []       xs = [xs]
splitManyBy (ys:yss) xs = case splitBy ys xs of (xs1, xs2) -> xs1 : splitManyBy yss xs2


splitAtRev :: Int -> [a] -> ([a], [a])
splitAtRev n xs = case splitAt n (reverse xs) of (xs1, xs2) -> (reverse xs2, reverse xs1)

takeFirst :: (a -> Bool) -> [a] -> (Maybe a, [a])
takeFirst p = takeFirstJust (\x -> guard (p x) >> return x)

takeFirstJust :: (a -> Maybe b) -> [a] -> (Maybe b, [a])
takeFirstJust _ [] = (Nothing, [])
takeFirstJust p (x:xs)
  | Just y <- p x = (Just y, xs)
  | otherwise     = second (x:) $ takeFirstJust p xs

expectJust :: String -> Maybe a -> a
expectJust _ (Just x) = x
expectJust s Nothing  = error $ "expectJust: " ++ s

safeFromLeft :: Either a b -> Maybe a
safeFromLeft (Left x) = Just x
safeFromLeft _        = Nothing

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

expectHead :: String -> [a] -> a
expectHead s = expectJust s . safeHead

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x
   | x' == x   = x
   | otherwise = fixpoint f x'
  where x' = f x
