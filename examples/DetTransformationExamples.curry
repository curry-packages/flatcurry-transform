------------------------------------------------------------------------------
--- This module contains a couple of simple but useful transformations
--- on FlatCurry expressions.
--- There are all entirely deterministic
------------------------------------------------------------------------------

module DetTransformationExamples (unDollarDet, unTypeDet, floatDet,
                                  floatOrDet, makeStrLitDet, toANFDet,
                                  caseCancelDet) where

import FlatCurry.Types

import FlatCurry.Transform.Types ( ExprTransformationDet, combine,
                                   makeTDet )

--- Transformation: remove `$` if the first argument is a known function
---
--- f $ x  ==>  f x
---
unDollarDet :: ExprTransformationDet
unDollarDet = makeTDet "UNDOLLAR" undollarRule

undollarRule :: Expr -> Maybe Expr
undollarRule e = 
  case e of
       Comb FuncCall ("Prelude","$") [(Comb (FuncPartCall n) f pargs), arg] ->
         case n of
           0 -> Nothing
           1 -> Just $ Comb FuncCall f (pargs++[arg])
           _ -> Just $ Comb (FuncPartCall (n-1)) f (pargs++[arg])
       _ -> Nothing 

--- Transformation: transform `Typed` expressions by removing type info.
---
--- (e :: t)  ==>  e
---
unTypeDet :: ExprTransformationDet
unTypeDet = makeTDet "UNTYPE" untypeRule

untypeRule :: Expr -> Maybe Expr
untypeRule exp = case exp of
                   (Typed e _) -> Just e
                   _           -> Nothing

--- Transformation: let floating, move nested let expressions?
--- as is {a1 = e1; a2 = e2; ...}
--- as bs is {a1 = e1; ... ak = e2; b1 = e_(k+1) ... }
---
--- float1
--- let x = let vs       let vs 
---         in e1    =>  in let x = e1
--- in e2                   in e2     
---
--- float2
--- let x = let vs free      let vs free
---         in e1        =>  in let x = e1
--- in e2                       in e2     
---
--- float3
--- let (as (x = let vs in e1) bs => let as bs vs (x = e1)
--- in e2                            in e2
---
--- float4
--- let as (x = let vs free in e1) bs    let vs free
--- in e2                             => in let as bs (x = e1)
---                                         in e2
---
--- float5,6,7,8
--- (let vs in e1) ? e2       => let vs in (e1 ? e2)
--- e1 ? (let vs in e2)       => let vs in (e1 ? e2)
--- (let vs free in e1) ? e2  => let vs free in (e1 ? e2)
--- e1 ? (let vs free in e2)  => let vs free in (e1 ? e2)
---
--- float9, float10
--- f (as (let vs in e) bs)      => let vs in f (as e bs)
--- f (as (let vs free in e) bs) => let vs free in f (as e bs)
---
--- float11, float12
--- case (let vs in e) of {...}      => let vs in case e of {...}
--- case (let vs free in e) of {...} => let vs free in case e of {...}


floatDet :: ExprTransformationDet
floatDet = combine (map (makeTDet "FLOAT")
                      [float1,float2,float3,float4,float5,float6,
                       float7,float8,float9,float10,float11,float12])

floatOrDet :: ExprTransformationDet
floatOrDet = combine (map (makeTDet "FLOAT OR") [float5,float6])

float1 :: Expr -> Maybe Expr
float1 e = case e of
                (Let [(x,(Let vs e1))] e2) -> 
                   Just $ Let vs (Let [(x,e1)] e2)
                _ -> Nothing

float2 :: Expr -> Maybe Expr
float2 e = case e of
                (Let [(x,(Free vs e1))] e2) -> 
                   Just $ Free vs (Let [(x,e1)] e2)
                _ -> Nothing

float3 :: Expr -> Maybe Expr
float3 e = case e of 
             Let vs e1 -> case findLet vs of 
                 Just (as,x,ys,e2,bs) ->
                     Just $ Let ((x,e2) : as++ys++bs) e1
                 _ -> Nothing
             _ -> Nothing

float4 :: Expr -> Maybe Expr
float4 e = case e of 
             Let vs e1 -> case findFree vs of 
                 Just (as,x,ys,e2,bs) ->
                   Just $ Free ys (Let ((x,e2):as++bs) e1)
                 _ -> Nothing
             _ -> Nothing

float5 :: Expr -> Maybe Expr
float5 e = case e of
                Or (Let vs e1) e2 -> 
                    Just $ Let vs (Or e1 e2)
                _ -> Nothing

float6 :: Expr -> Maybe Expr
float6 e = case e of
                Or e1 (Let vs e2) -> 
                    Just $ Let vs (Or e1 e2)
                _ -> Nothing

float7 :: Expr -> Maybe Expr
float7 e = case e of
                Or (Free vs e1) e2 -> 
                    Just $ Free vs (Or e1 e2)
                _ -> Nothing

float8 :: Expr -> Maybe Expr
float8 e = case e of
                Or e1 (Free vs e2) -> 
                    Just $ Free vs (Or e1 e2)
                _ -> Nothing

float9 :: Expr -> Maybe Expr
float9 exp = case exp of 
                Comb ct n es -> 
                  case findLetE es of 
                    Just (as,vs,e,bs) -> 
                      Just $ Let vs (Comb ct n (as++[e]++bs))
                    Nothing -> Nothing
                _ -> Nothing

float10 :: Expr -> Maybe Expr
float10 exp = case exp of 
                Comb ct n es -> 
                  case findFreeE es of 
                    Just (as,vs,e,bs) -> 
                      Just $ Free vs (Comb ct n (as++[e]++bs))
                    Nothing -> Nothing
                _ -> Nothing

float11 :: Expr -> Maybe Expr
float11 exp = case exp of
                Case ct (Let vs e) bs -> Just $ Let vs (Case ct e bs)
                _ -> Nothing

float12 :: Expr -> Maybe Expr
float12 exp = case exp of
                Case ct (Free vs e) bs -> Just $ Free vs (Case ct e bs)
                _ -> Nothing

--isLit e = case e of
--               Lit _ -> True
--               _     -> False
--
--isVar e = case e of
--               Var _ -> True
--               _     -> False
--
--isLet e = case e of
--               Let _ _ -> True
--               _       -> False
--
--isFree e = case e of
--                Free _ _ -> True
--                _        -> False
--
--isOr e = case e of
--              Or _ _ -> True
--              _      -> False
--
--isComb e = case e of
--                Comb _ _ _ -> True
--                _          -> False
--
--isCase e = case e of
--                Comb _ _ _ -> True
--                _          -> False
--
--isTyped e = case e of
--                 Comb _ _ _ -> True
--                 _          -> False
--
--find :: (Expr -> Bool) -> [Expr] -> Maybe (Expr,[Expr])
--find p []     = Nothing
--find p (e:es)
-- | p e        = Just (e,es)
-- | otherwise  = do (x,xs) <- find p es
--                   Just (x,e:xs)
--
--findBind :: (Expr -> Bool) -> [(VarIndex,Expr)] 
--         -> Maybe (VarIndex,Expr,[(VarIndex,Expr)])
--findBind p []         = Nothing
--findBind p ((v,e):vs) 
-- | p e                = Just (v,e,vs)
-- | otherwise          = do (v',e',vs') <- findBind p vs
--                           Just (v',e',(v,e):vs')

findLet :: [(VarIndex,Expr)] -> Maybe ([(VarIndex,Expr)], 
                                       VarIndex,
                                       [(VarIndex,Expr)],
                                       Expr,
                                       [(VarIndex,Expr)])
findLet [] = Nothing
findLet ((x,e):es) = case e of
                          Let vs e' -> Just ([],x,vs,e',es)
                          _ -> case findLet es of
                                    Nothing -> Nothing
                                    Just (as,y,vs,e',bs) -> 
                                      Just ((x,e):as,y,vs,e',bs)

findLetE :: [Expr] -> Maybe ([Expr], [(VarIndex,Expr)], Expr, [Expr])
findLetE [] = Nothing
findLetE (e:es) = case e of
                       Let vs e' -> Just ([],vs,e',es)
                       _ -> case findLetE es of
                                    Nothing -> Nothing
                                    Just (as,vs,e',bs) -> 
                                      Just (e:as,vs,e',bs)
                          
findFree :: [(a, Expr)] -> Maybe ([(a, Expr)], a, [Int], Expr, [(a, Expr)])
findFree [] = Nothing
findFree ((x,e):es) = case e of
                           Free vs e' -> Just ([],x,vs,e',es)
                           _ -> case findFree es of
                                     Nothing -> Nothing
                                     Just (as,y,vs,e',bs) -> 
                                       Just ((x,e):as,y,vs,e',bs)

findFreeE :: [Expr] -> Maybe ([Expr], [VarIndex], Expr, [Expr])
findFreeE [] = Nothing
findFreeE (e:es) = case e of
                        Free vs e' -> Just ([],vs,e',es)
                        _ -> case findFreeE es of
                                     Nothing -> Nothing
                                     Just (as,vs,e',bs) -> 
                                       Just (e:as,vs,e',bs)

--------------------------------------------------------------------
--- Make String Literal
---
--- translates strings in list form to be a single constructor with
--- no arugments.
---
--- example 'h' : 'e' : 'l' : 'l' : 'o'
--- becomes StringConst.hello
--- In FlatCurry this is (Comb ConsCall ("StringConst","hello") [])
--------------------------------------------------------------------

makeStrLitDet :: ExprTransformationDet
makeStrLitDet = makeTDet "STRING" strLitDet

strLitDet :: Expr -> Maybe Expr
strLitDet e = case e of 
               Comb ConsCall ("Prelude",":") [Lit (Charc c), str] ->
                case str of
                  Comb ConsCall ("Prelude","[]")   [] -> Just $ strConst [c]
                  Comb ConsCall ("StringConst",cs) [] -> Just $ strConst (c:cs)
                  _ -> Nothing
               _ -> Nothing

strConst :: String -> Expr
strConst x = Comb ConsCall ("StringConst",x) []

-----------------------------------------------------------
---
--- Transform expresion to A-Normal Form
---
--- e is a non-trivial expression
--- v is a trivial expression
--- n is a fresh variable
---
--- case e of bs => let n = e in case n of bs
--- f (vs e es)  => let n = e in f (vs n es)
--- e1 ? e2      => let n = e1 in n ? e2
--- v1 ? e2      => let n = e2 in v1 ? e2
-----------------------------------------------------------

toANFDet :: ExprTransformationDet
toANFDet (n,_) e = 
  case e of
    Case ct e' bs ->
      if not (trivial e') 
        then Just (Let [(n,e')] (Case ct (Var n) bs), "ANF_CASE", 1)
        else Nothing
    Comb ct n1 es ->
      do (as,e',bs) <- firstNonTriv es
         return (Let [(n,e')] (Comb ct n1 (as++[Var n]++bs)), "ANF_APP", 1)

    Or e1 e2 ->
      if not (trivial e1) 
      then Just (Let [(n,e1)] (Or (Var n) e2), "ANF_OR1", 1)
      else if not (trivial e2) 
           then Just (Let [(n,e2)] (Or e1 (Var n)), "ANF_OR2", 1)
           else Nothing
    _ -> Nothing

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

-----------------------------------------------------------

caseCancelDet :: ExprTransformationDet
caseCancelDet = combine [makeTDet "CASE CANCEL CONS" caseCon,
                         makeTDet "CASE CANCEL LIT"  caseLit]


caseLit :: Expr -> Maybe Expr
caseLit exp = case exp of
                Case _ (Lit l) bs -> findBranch l bs
                _                 -> Nothing
 where findBranch _ [] = Nothing
       findBranch l (Branch (LPattern p) e : bs)
         | l == p    = Just e
         | otherwise = findBranch l bs

caseCon :: Expr -> Maybe Expr
caseCon exp = case exp of
                Case _ (Comb ConsCall n []) bs -> findBranch n bs
                _                              -> Nothing
 where findBranch _ [] = Nothing
       findBranch n (Branch (Pattern p vs) e : bs)
         | n == p && null vs = Just e
         | otherwise         = findBranch n bs
