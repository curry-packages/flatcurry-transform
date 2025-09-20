------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: September 2025
--
-- This module contains a couple of simple but useful transformations
-- on FlatCurry expressions.
------------------------------------------------------------------------------
{-# OPTIONS_FRONTEND -Wno-incomplete-patterns -Wno-overlapping #-}

module Transformations
  ( transTestModule, runTransform
  , removeQuestion, unType, unDollar, caseCancel
  , float, floatOr, makeStrLit, toANF
  )
 where

import FlatCurry.Files   ( readFlatCurry )
import FlatCurry.Pretty  ( defaultOptions, ppProg )
import FlatCurry.Types
import Text.Pretty       ( pPrint )

import FlatCurry.Transform.Exec  ( transformFuncsInProg )
import FlatCurry.Transform.Types ( ExprTransformation, makeT )

------------------------------------------------------------------------------
-- A simple operation to test transformations on FlatCurry programs.
-- It applies the transformation (first argument) to the module
-- (second argument) and shows the original and transformed FlatCurry program
-- in pretty-printed form.
runTransform :: ExprTransformation -> String -> IO ()
runTransform exptrans mname = do
  fprog <- readFlatCurry mname
  printProg "ORIGINAL PROGRAM:" fprog
  let tprog = transformFuncsInProg (\() -> exptrans) fprog
  printProg "TRANSFORMED PROGRAM:" tprog
 where
  printProg title fprog = do
    putStr $ unlines $ [replicate 70 '=', title, replicate 70 '=']
    putStrLn $ pPrint $ ppProg defaultOptions fprog

-- Transform the program `TestModule.curry` with three simple transformations.
transTestModule :: IO ()
transTestModule = runTransform (unDollar ? unType ? caseCancel) "TestModule"

------------------------------------------------------------------------------
-- Transform calls to `Prelude.?` into FlatCurry choice nodes.
--
removeQuestion :: ExprTransformation
removeQuestion = makeT "REMOVE-?-CAll" removeQuestionRule

removeQuestionRule :: Expr -> Expr
removeQuestionRule (Comb FuncCall ("Prelude","?") [e1,e2]) = Or e1 e2

------------------------------------------------------------------------------
-- Transform `Typed` expressions by removing type info, i.e.,
--
--     (e :: t)  ==>  e
--
unType :: ExprTransformation
unType = makeT "UNTYPE" unTypeRule

unTypeRule :: Expr -> Expr
unTypeRule (Typed e _) = e

------------------------------------------------------------------------------
-- Transformation: remove `$` if the first argument is a known function
--
-- f $ x  ==>  f x
--
unDollar :: ExprTransformation
unDollar = makeT "UNDOLLAR" unDollarRule

unDollarRule :: Expr -> Expr
unDollarRule (dollar f args miss x) 
 | miss == 1 = Comb FuncCall f (args++[x])
 | miss > 1  = Comb (FuncPartCall (miss-1)) f (args ++ [x])

dollar :: QName -> [Expr] -> Int -> Expr -> Expr
dollar f args miss x = Comb FuncCall ("Prelude","$")
                            [Comb (FuncPartCall miss) f args, x]

------------------------------------------------------------------------------
-- Transformation: simplify case expressions with constant values
--
-- case C of { ... ; C -> e ; ... }  ==>  e
--
caseCancel :: ExprTransformation
caseCancel = makeT "CASE CANCEL" caseCancelRule

caseCancelRule :: Expr -> Expr
caseCancelRule (Case _ (Lit l) (litBranch l e)) = e
caseCancelRule (Case _ (Comb ConsCall n []) (conBranch n e)) = e

litBranch :: Literal -> Expr -> [BranchExpr]
litBranch l e = (_++[Branch (LPattern l) e]++_)

conBranch :: QName -> Expr -> [BranchExpr]
conBranch n e = (_++[Branch (Pattern n []) e]++_)

------------------------------------------------------------------
-- Transformation: let floating, move nested let expressions

float :: ExprTransformation
float = makeT "FLOAT" floatR

floatR :: Expr -> Expr
floatR (Let [(x,(Let ys e1))] e2)          = Let ys (Let [(x,e1)] e2)
floatR (Let [(x,(Free vs e1))] e2)         = Free vs (Let [(x,e1)] e2)
floatR (Let (as++[(x,Let vs e1)]++bs) e2)  = Let ((x,e1):as++vs++bs) e2
floatR (Let (as++[(x,Free vs e1)]++bs) e2) = Free vs (Let ((x,e1):as++bs) e2)
floatR (Or (Let vs e1) e2)                 = Let vs (Or e1 e2)
floatR (Or e1 (Let vs e2))                 = Let vs (Or e1 e2)
floatR (Or (Free vs e1) e2)                = Free vs (Or e1 e2)
floatR (Or e1 (Free vs e2))                = Free vs (Or e1 e2)
floatR (Comb ct n (as++[Let vs e]++bs))    = Let vs (Comb ct n (as++[e]++bs))
floatR (Comb ct n (as++[Free vs e]++bs))   = Free vs (Comb ct n (as++[e]++bs))
floatR (Case ct (Let vs e) bs)             = Let vs (Case ct e bs)
floatR (Case ct (Free vs e) bs)            = Free vs (Case ct e bs)

-- Transformation: move nested let expressions out of choices, i.e.,
--
--     (let vs in e1) ? e2       => let vs in (e1 ? e2)
--     e1 ? (let vs in e2)       => let vs in (e1 ? e2)
--
floatOr :: ExprTransformation
floatOr = makeT "FLOAT OR" floatR

floatOrR :: Expr -> Expr
floatOrR (Or (Let vs e1) e2) = Let vs (Or e1 e2)
floatOrR (Or e1 (Let vs e2)) = Let vs (Or e1 e2)

------------------------------------------------------------------------------
-- Transform a string literal, i.e., a finite list of characters,
-- into a single constant represented in FlatCurry by
--
--     Comb ConsCall ("StringConst",s) []
--
-- (where `s` is the actual string).
makeStrLit :: ExprTransformation
makeStrLit = makeT "STRING" makeStrLitRule

makeStrLitRule :: Expr -> Expr
makeStrLitRule (strCons c (strNil   ())) = strConst [c]
makeStrLitRule (strCons c (strConst x))  = strConst (c:x)

strCons :: Char -> Expr -> Expr
strCons c str = Comb ConsCall ("Prelude",":") [Lit (Charc c), str]

strNil :: () -> Expr
strNil    ()  = Comb ConsCall ("Prelude","[]") []

strConst :: String -> Expr
strConst x = Comb ConsCall ("StringConst",x) []

------------------------------------------------------------------------------
-- Transform an expression to its A-Normal Form, i.e., perform
-- the following transformations, where
-- e is a non-trivial expression,
-- v is a trivial expression, and
-- n is a fresh variable:
--
--     case e of bs  =>  let n = e in case n of bs
--     f (vs e es)   =>  let n = e in f (vs n es)
--     e1 ? e2       =>  let n = e1 in n ? e2
--     v1 ? e2       =>  let n = e2 in v1 ? e2
--
toANF :: ExprTransformation
toANF (n,_) (Case ct e bs)
 | not (trivial e) = (Let [(n,e)] (Case ct (Var n) bs), "ANF CASE", 1)

{-
-- Note: this formulation does not work in KiCS2 since the functional
-- pattern might contain float constants for which no generator exists:
toANF (n,_) (Comb ct n1 (as++[e]++bs))
 | all trivial as && not (trivial e) 
 = (Let [(n,e)] (Comb ct n1 (as++[Var n]++bs)), "ANF APP", 1)
-}
toANF (n,_) (Comb ct n1 es) =
  maybe failed
    (\(as,e,bs) -> (Let [(n,e)] (Comb ct n1 (as++[Var n]++bs)), "ANF APP", 1))
    (firstNonTriv es)

toANF (n,_) (Or e1 e2)
 | not (trivial e1) = (Let [(n,e1)] (Or (Var n) e2), "ANF ORL", 1)
 | not (trivial e2) = (Let [(n,e2)] (Or e1 (Var n)), "ANF ORR", 1)

-- Returns the first non-trivial expression from a list of expressions.
firstNonTriv :: [Expr] -> Maybe ([Expr], Expr, [Expr])
firstNonTriv []                        = Nothing
firstNonTriv (e:es) | not (trivial e)  = Just ([],e,es)
                    | otherwise        = do (as,e',bs) <- firstNonTriv es
                                            Just (e:as,e',bs)

-- Is an expression trival?
trivial :: Expr -> Bool
trivial (Var _)      = True
trivial (Lit _)      = True
trivial (Comb _ _ _) = False
trivial (Let _ _)    = False
trivial (Free _ _)   = False
trivial (Or _ _)     = False
trivial (Typed _ _)  = False
trivial (Case _ _ _) = False

------------------------------------------------------------------------------
