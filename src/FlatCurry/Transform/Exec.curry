------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: August 2025
--
-- Implementation of transforming FlatCurry expressions by applying
-- non-deterministically defined expressions transformations
-- as long as possible.
------------------------------------------------------------------------------

module FlatCurry.Transform.Exec
  ( transformExpr, transformExprN, showTransformExpr )
 where

import Control.Search.Unsafe ( oneValue )

import FlatCurry.Types
import FlatCurry.Pretty      ( ppExp, Options(..), QualMode(..) )
import Text.Pretty           ( pPrint )

import FlatCurry.Transform.Types
import FlatCurry.Transform.Utils

-- Loop over each function and apply a specified transformation.
-- The transformation is allowed to return an empty list
-- if no transformation is applied
-- However, if any transformation is applied, then the transformed functions are
-- passed into opt again to see if they can be transformed further.
--
-- @param opt - the transformationto apply to each function
--              returns an empty list if no transformation is applied
--              otherwise it returns a list of 1 or more transformed functions
-- @param (f:fs) - the list of funcions to apply the transformation
-- @return a list of transformed functions.  This list may be longer than the origonal list.
loop :: (Int -> FuncDecl -> [FuncDecl]) -> Int -> [FuncDecl] -> [FuncDecl]
loop _   _ []     = []
loop opt n (f:fs)
  = fcase opt n f of
      []      -> f : loop opt n fs
      y@(_:_) -> loop opt (n+1) (y++fs)

loopIO :: (Int -> FuncDecl -> IO [FuncDecl]) -> Int -> [FuncDecl]
       -> IO [FuncDecl]
loopIO _   _ []     = return []
loopIO opt n (f:fs) = do y <- opt n f
                         if null y
                           then do fs' <- loopIO opt n fs
                                   return (f:fs')
                           else loopIO opt (n+1) (y++fs)

------------------------------------------------------------------------------
-- | Simplifies a FlatCurry expression according to some expression
--   transformation.
--   Since the expression transformation can be non-deterministically
--   defined, we pass it as a function which is similarly to passing it
--   via run-time choice.
--   The second argument is the maximum number of transformation steps
--   to be applied. If the number is `-1`, then keep going until
--   no transformation can be applied.
---
--   Although the single transformation steps can be non-deterministic,
--   the strategy to apply such steps is deterministic since it is applied
--   in a bottom-up manner: if there is some node to be transformed,
--   all child nodes are transformed before transformation rules are applied
--   to the node itself.
transformExpr :: (() -> ExprTransformation) -> Int -> Expr -> Expr
transformExpr trans n e = fst (runTrExpr trans n (newVar e) e)

-- | The same as 'transformExpr' but return also the number of applied
--   transformation steps.
transformExprN :: (() -> ExprTransformation) -> Int -> Expr -> (Expr,Int)
transformExprN trans n e =
  let (e',steps) = runTrExpr trans n (newVar e) e
  in (e', length steps)

showTransformExpr :: (() -> ExprTransformation) -> Int -> Expr
                  -> (Expr,String,Int)
showTransformExpr trans n e = let (e',steps) = runTrExpr trans n (newVar e) e
                              in (e', reconstruct e steps, length steps)

-- Apply an expression transformation (with a maximum number of steps
-- and a fresh variable index) to an expression and return the
-- transformed expression and the list of applied transformation steps.
runTrExpr :: (() -> ExprTransformation) -> Int -> VarIndex -> Expr
          -> (Expr,[Step])
runTrExpr trans n v e
 | n == 0    = (e,[])
 | otherwise = let (e', s, v', seen) = runRewriter (run trans [] e) v
               in case seen of
                    False -> (e', s)
                    True  -> mapSnd (s++) $ runTrExpr trans (n-1) v' e'

run :: (() -> ExprTransformation) -> Path -> Expr -> ReWriter Expr
run _ _ e@(Var _) = return e
run _ _ e@(Lit _) = return e

run trans p (Comb ct n es) = do es' <- mapM runExp (zip [0..] es)
                                runExprTransform trans p (Comb ct n es')
 where runExp (i,e) = run trans (i:p) e

run trans p (Let vs e) = do e'  <- run trans (-1:p) e
                            vs' <- mapM runVar (zip [0..] vs)
                            runExprTransform trans p (Let vs' e')
 where runVar (n,(v,l)) = do l' <- run trans (n:p) l
                             return (v,l')

run trans p (Free vs e) = do e' <- run trans (0:p) e
                             runExprTransform trans p (Free vs e')

run trans p (Or e1 e2) = do e1' <- run trans (0:p) e1
                            e2' <- run trans (1:p) e2
                            runExprTransform trans p (Or e1' e2')

run trans p (Case ct e bs) = do e'  <- run trans (-1:p) e
                                bs' <- mapM runBranch (zip [0..] bs)
                                runExprTransform trans p (Case ct e' bs')
 where runBranch (n,Branch q b) = do b' <- run trans (n:p) b
                                     return (Branch q b')

run trans p (Typed e te) = do e' <- run trans (0:p) e
                              runExprTransform trans p (Typed e' te)

-- Apply a (usually partially defined) expression transformation
-- to an expression.
runExprTransform :: (() -> ExprTransformation) -> Path -> Expr -> ReWriter Expr
runExprTransform trans p e = do
  v <- curVar
  case oneValue (trans () (v,p) e) of
    Nothing        -> return e
    Just (e',r,dv) -> do update e' (r,p,e') dv
                         run trans p e'

reconstruct :: Expr -> [Step] -> String
reconstruct _ [] = ""
reconstruct e ((rule, p, rhs):steps) =
  "=> " ++ rule ++ " " ++ show (reverse p) ++ "\n" ++
  pPrint (ppExp (Options 2 QualNone "") e') ++ "\n" ++
  reconstruct e' steps
 where
  e' = replace e (reverse p) rhs

-- helper functions to make some expressions easier to construct
applyf :: Expr -> [Expr] -> Expr
applyf f es = Comb FuncCall ("Prelude","apply") (f:es)

comp :: Expr -> Expr -> Expr
comp f g = Comb (FuncPartCall 1) ("Prelude",".") [f,g]

caseBranch :: Expr -> Expr
caseBranch e = Case _ _ (_++[Branch _ e]++_)

partCall :: Int -> QName -> [Expr] -> Expr
partCall n f es = Comb (FuncPartCall n) f es
                ? Comb (ConsPartCall n) f es

has :: Expr -> Expr
has e = e
      ? (Comb _ _ (_ ++ [has e] ++ _))
      ? (Let (_ ++ [(_, has e)] ++ _) _)
      ? (Let _ (has e))
      ? (Free _ (has e))
      ? (Or (has e) _)
      ? (Or _ (has e))
      ? (Case _ _ (_ ++ [(Branch _ (has e))] ++ _))
      ? (Case _ (has e) _)
