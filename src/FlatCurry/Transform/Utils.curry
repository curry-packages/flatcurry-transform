------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: September 2025
--
--  Utility operations to execute program transformations.
------------------------------------------------------------------------------
{-# OPTIONS_FRONTEND -Wno-incomplete-patterns #-}

module FlatCurry.Transform.Utils
  ( ReWriter(..), curVar, newVar, replace, update )
 where

import Control.Monad.Trans.State
import FlatCurry.Types
import FlatCurry.Goodies ( branchExpr )
import Data.List         ( sort, sum )

import FlatCurry.Transform.Types

------------------------------------------------------------------------------
-- | Replace a subexpression in an expressions, i.e.,
--   `replace e p w` implements `e[w]_p`.
replace :: Expr -> Path -> Expr -> Expr
replace _             []     w = w
replace (Free vs e)   (0:ps) w = Free vs (replace e ps w)
replace (Or e1 e2)    (0:ps) w = Or (replace e1 ps w) e2
replace (Or e1 e2)    (1:ps) w = Or e1 (replace e2 ps w)
replace (Typed e t)   (0:ps) w = Typed (replace e ps w) t

replace (Comb t n es) (p:ps) w = Comb t n (x ++ [replace e ps w] ++ y)
  where (x,e:y) = splitAt p es

replace (Let bs e) (p:ps) w 
 | p == -1   = Let bs  (replace e ps w)
 | otherwise = Let bs' e
  where (x, (v,ve):y) = splitAt p bs
        bs' = (x ++ [(v, replace ve ps w)] ++ y)

replace (Case t e bs) (p:ps) w
 | p == -1   = Case t (replace e ps w) bs
 | otherwise = Case t e bs'
  where (x, (Branch f be):y) = splitAt p bs
        bs' = (x ++ [Branch f (replace be ps w)] ++ y)

------------------------------------------------------------------------------
-- | Returns the next unused variable index in an expression.
newVar :: Expr -> VarIndex
newVar (Var v)       = v+1
newVar (Lit _)       = 1
newVar (Comb _ _ es) = foldr (max . newVar) 1 es
newVar (Free vs e)   = max (max1 vs + 1) (newVar e)
newVar (Or e1 e2)    = max (newVar e1) (newVar e2)
newVar (Typed e _)   = newVar e
newVar (Let vs e)    = max (newVar e) (foldr maxLet 1 vs)
 where maxLet (v,le) m = m `max` (v+1) `max` newVar le
newVar (Case _ e bs) = max (newVar e) (foldr (max . maxBranch) 1 bs)
 where maxBranch (Branch (Pattern _ vs) be) = max (max1 vs + 1) (newVar be)
       maxBranch (Branch (LPattern _) be)   = newVar be

max1 :: [Int] -> Int
max1 = foldr max 0

------------------------------------------------------------------------------
-- The type `ReWriter` is an extension of the Writer monad
-- It is used to execute program transformations.
newtype ReWriter a =
  ReWriter { runRewriter :: VarIndex -> (a, [Step], VarIndex, Bool) }

instance Functor ReWriter
 where
  fmap _ _ = error "ReWriter.fmap"

instance Applicative ReWriter where
  pure x = ReWriter $ \v -> (x,[],v,False)
  _ <*> _ = error "ReWriter.<*>"

instance Monad ReWriter where
 return = pure
 (ReWriter h) >>= f 
  = ReWriter $ \v -> 
     case h v of 
      (e1, steps1, v1, seen1) -> 
       case f e1 of
        (ReWriter g) ->
         case g v1 of
          (e2, steps2, v2, seen2) -> (e2, steps1 ++ steps2, v2, seen1 || seen2)


curVar :: ReWriter VarIndex
curVar = ReWriter $ \v -> (v,[],v,False)

update :: a -> Step -> VarIndex -> ReWriter a
update e step dv = ReWriter $ \v -> case v+dv of
                                      n -> (e, [step], n, True)

------------------------------------------------------------------------------
