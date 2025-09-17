------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: August 2025
--
-- Implementation of transforming FlatCurry expressions by applying
-- non-deterministically defined expressions transformations
-- as long as possible with a chaotic (non-deterministic) strategy.
------------------------------------------------------------------------------
{-# OPTIONS_FRONTEND -Wno-incomplete-patterns -Wno-overlapping #-}

module FlatCurry.Transform.ExecND
  ( transformExprND )
 where

import Control.Search.Unsafe ( oneValue )

import FlatCurry.Types

import FlatCurry.Transform.Types
import FlatCurry.Transform.Utils ( newVar )

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
--   To apply transformation steps, a subexpression is non-deterministically
--   selected.
transformExprND :: (() -> ExprTransformation) -> Int -> Expr -> Expr
transformExprND trans n e = runTrExprND trans n (newVar e) e

runTrExprND :: (() -> ExprTransformation) -> Int -> VarIndex -> Expr -> Expr
runTrExprND trans n nvar exp
  | n == 0    = exp
  | otherwise = case oneValue (tryTransExpr nvar exp) of
                  Nothing -> exp -- no transformation applicable
                  Just (p, (e',_,nvs)) -> runTrExprND trans (n-1) (nvar+nvs)
                                            (replace exp p e')
 where
  tryTransExpr v e = let (p,se) = subExpOf e
                     in (p, trans () (v,p) se)

-- Non-deterministically return some subexpression with its path.
subExpOf :: Expr -> (Path,Expr)
subExpOf e = ([],e) -- the subexpression is the entire expression
subExpOf (Comb _ _ args) =
  uncurry extendPath $ anyOf (zip [0..] (map subExpOf args))
subExpOf (Let _  e) = extendPath 0 (subExpOf e)
subExpOf (Let bs _) =
  uncurry extendPath $ anyOf (zip [1..] (map (subExpOf . snd) bs))
subExpOf (Free _ e) = extendPath 1 (subExpOf e)
subExpOf (Or e1 e2) = extendPath 0 (subExpOf e1) ? extendPath 1 (subExpOf e2)
subExpOf (Case _ ce _) = extendPath 0 (subExpOf ce)
subExpOf (Case _ _ bs) =
  uncurry extendPath $ anyOf (zip [1..] (map (subExpOf . branchExp) bs))
 where branchExp (Branch _ be) = be
subExpOf (Typed e _) = extendPath 0 (subExpOf e)

extendPath :: Int -> (Path,Expr) -> (Path,Expr)
extendPath pos (p,e) = (pos:p, e)

-- Replace a subexpression of an expression at a given position (path).
replace :: Expr -> Path -> Expr -> Expr
replace _ [] e' = e' -- replace at root
replace (Comb ct qf args) (pos:p) e' =
  Comb ct qf (updateListElem args pos (replace (args!!pos) p e'))
replace (Let bs e) (pos:p) e'
  | pos == 0  = Let bs (replace e p e')
  | otherwise = let p1 = pos - 1 in
                Let (updateListElem bs p1
                       (let (v,be) = bs!!p1 in (v, replace be p e')))
                    e
replace (Free vs e) (1:p) e' = Free vs (replace e p e')
replace (Or e1 e2) (0:p) e' = Or (replace e1 p e') e2
replace (Or e1 e2) (1:p) e' = Or e1 (replace e2 p e')
replace (Case ct ce bs) (pos:p) e'
  | pos == 0  = Case ct (replace ce p e') bs
  | otherwise = let p1 = pos - 1 in
                Case ct ce
                 (updateListElem bs p1
                  (let (Branch pt be) = bs!!p1 in Branch pt (replace be p e')))
replace (Typed e te) (0:p) e' = Typed (replace e p e') te

updateListElem :: [a] -> Int -> a -> [a]
updateListElem (x:xs) i y | i == 0 = y:xs
                          | i > 0  = x : updateListElem xs (i-1) y
updateListElem [] _ _ = error "updateListElem applied to empty list"

------------------------------------------------------------------------------
