------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: September 2025
--
-- Implementation of transforming FlatCurry expressions by applying
-- deterministically defined expressions transformations as long as possible.
------------------------------------------------------------------------------

module FlatCurry.Transform.ExecDet
  ( transformExprDet, showTransformExprDet )
 where

import Data.Tuple.Extra      ( second )
import FlatCurry.Types
import FlatCurry.Pretty      ( ppExp, Options(..), QualMode(..) )
import Text.Pretty           ( pPrint )

import FlatCurry.Transform.Types
import FlatCurry.Transform.Utils ( ReWriter(..)
                                 , curVar, newVar, replace, update )

------------------------------------------------------------------------------
-- | Simplifies an expression according to some expression transformation.
--   Since the expression transformation can be non-deterministically
--   defined, we pass it as a function which is similarly to passing it
--   via run-time choice.
--   The second argument is the maximum number of transformation steps
--   to be applied. If the number is `-1`, then keep going until
--   no transformation can be applied.
transformExprDet :: ExprTransformationDet -> Int -> Expr -> Expr
transformExprDet trans n e = fst (runTrExpr trans n (newVar e) e)

showTransformExprDet :: ExprTransformationDet -> Int -> Expr
                     -> (Expr,String,Int)
showTransformExprDet trans n e 
  = let (e',steps) = runTrExpr trans n (newVar e) e
    in (e', reconstruct e steps, length steps)

runTrExpr :: ExprTransformationDet -> Int -> VarIndex 
             -> Expr -> (Expr,[Step])
runTrExpr trans n v e
 | n == 0    = (e,[])
 | otherwise = let (e', s, v', seen) = runRewriter (run trans [] e) v
               in case seen of
                    False -> (e', s)
                    True  -> second (s++) $ runTrExpr trans (n-1) v' e'

run :: ExprTransformationDet -> Path -> Expr -> ReWriter Expr
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

-- Apply a totally defined expression transformation
-- to an expression.
runExprTransform :: ExprTransformationDet -> Path -> Expr -> ReWriter Expr
runExprTransform trans p e = do
  v <- curVar
  case trans (v,p) e of
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
