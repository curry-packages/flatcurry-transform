------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: September 2025
--
-- Implementation of transforming FlatCurry expressions by applying
-- partially and non-deterministically defined expression transformations
-- as long as possible.
------------------------------------------------------------------------------

module FlatCurry.Transform.Exec
  ( transformExpr, transformExprMax, transformExprN, showTransformExpr )
 where

import Control.Search.Unsafe ( oneValue )

import Data.Tuple.Extra      ( second )
import FlatCurry.Types
import FlatCurry.Pretty      ( ppExp, Options(..), QualMode(..) )
import Text.Pretty           ( pPrint )

import FlatCurry.Transform.Types
import FlatCurry.Transform.Utils ( ReWriter(..)
                                 , curVar, newVar, replace, update )

------------------------------------------------------------------------------
-- | Simplifies a FlatCurry expression according to some expression
--   transformation which can be partially or non-deterministically defined.
--   Since the expression transformation might be non-deterministic,
--   we pass it as a function which is similarly to passing it
--   via run-time choice.
--
--   Although the single transformation steps can be non-deterministic,
--   the strategy to apply such steps is deterministic since it is applied
--   in a bottom-up manner: if there is some node to be transformed,
--   all child nodes are transformed before transformation rules are applied
--   to the node itself.
transformExpr :: (() -> ExprTransformation) -> Expr -> Expr
transformExpr = transformExprMax (-1)

-- | The same as 'transformExpr' but takes the maximum number of
--   transformation steps to be applied as a further argument.
--   If the number is negative, then keep going until no transformation
--   can be applied.
transformExprMax :: Int -> (() -> ExprTransformation) -> Expr -> Expr
transformExprMax n trans e = fst (runTrExpr trans n (newVar e) e)

-- | The same as 'transformExprMax' but returns also the number of applied
--   transformation steps.
transformExprN :: Int -> (() -> ExprTransformation) -> Expr -> (Expr,Int)
transformExprN n trans e =
  let (e',steps) = runTrExpr trans n (newVar e) e
  in (e', length steps)

-- | The same as 'transformExprMax' but returns also a formatted trace of
--   all applied transformation steps as well as its total number.
showTransformExpr :: Int -> (() -> ExprTransformation) -> Expr
                  -> (Expr,String,Int)
showTransformExpr n trans e = let (e',steps) = runTrExpr trans n (newVar e) e
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
                    True  -> second (s++) $ runTrExpr trans (n-1) v' e'

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

------------------------------------------------------------------------------
