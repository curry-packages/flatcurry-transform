------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: August 2025
--
--  Utility operations for transformations.
--- TODO: restructure it, e.g., some operations are goodies for FlatCurry.
------------------------------------------------------------------------------
{-# OPTIONS_FRONTEND -Wno-incomplete-patterns #-}

module FlatCurry.Transform.Utils where

import Control.Monad.Trans.State
import FlatCurry.Types
import FlatCurry.Goodies ( branchExpr )
import Data.List         ( sort, sum )

import FlatCurry.Transform.Types

infixr 5 ++-, \\-, &&-

-------------------------------------------------------------
-- Function level tools
-------------------------------------------------------------

-- returns true if f is called recursively.
-- This does not handle mutual recursion.
recursiveFunc :: FuncDecl -> Bool
recursiveFunc (Func _ _ _ _ (External _)) = False
recursiveFunc (Func n _ _ _ (Rule _ b)) = recFunc n b
 where
   recFunc _ (Var _)       = False
   recFunc _ (Lit _)       = False
   recFunc f (Comb _ g es) = f == g || any (recFunc f) es
   recFunc f (Or e1 e2)    = any (recFunc f) [e1,e2]
   recFunc f (Typed e _)   = recFunc f e
   recFunc f (Free _ e)    = recFunc f e
   recFunc f (Let vs e)    = any (recFunc f) (e : map snd vs)
   recFunc f (Case _ e bs) = any (recFunc f) (e : map branchExpr bs)


-- returns list of every function that is called in the program.
funcCalls :: FuncDecl -> [QName]
funcCalls (Func _ _ _ _ (External _)) = []
funcCalls (Func _ _ _ _ (Rule _ b)) = getCalls b
 where 
   getCalls (Var _)        = []
   getCalls (Lit _)        = []
   getCalls (Let vs e)     = mergeMap (getCalls . snd) vs ++- getCalls e
   getCalls (Or e1 e2)     = getCalls e1 ++- getCalls e2
   getCalls (Free _ e)     = getCalls e
   getCalls (Comb ct n es) = if isFunc ct
                             then [n] ++- mergeMap getCalls es
                             else mergeMap getCalls es
   getCalls (Case _ e bs)  = getCalls e ++- mergeMap (getCalls . branchExpr) bs
   getCalls (Typed e _)    = getCalls e


isFunc :: CombType -> Bool
isFunc FuncCall         = True
isFunc (FuncPartCall _) = True
isFunc ConsCall         = False
isFunc (ConsPartCall _) = False

isCons :: CombType -> Bool
isCons = not . isFunc

isPart :: CombType -> Bool
isPart FuncCall         = False
isPart (FuncPartCall _) = True
isPart ConsCall         = False
isPart (ConsPartCall _) = True

isApp :: CombType -> Bool
isApp = not . isPart


-------------------------------------------------------------
-- expression level tools
-------------------------------------------------------------


-- check if a function is really a partial application in disguise.
-- They could be hinding under lets or frees
-- I'll allow hinding under choice only if the two branches are missing the same number of expressions.
-- I'm not sure if I should allow case expressions.
missingVars :: Expr -> Int
missingVars (Var _)                     = 0
missingVars (Lit _)                     = 0
missingVars (Comb FuncCall _ _)         = 0
missingVars (Comb ConsCall _ _)         = 0
missingVars (Comb (FuncPartCall n) _ _) = n
missingVars (Comb (ConsPartCall n) _ _) = n
missingVars (Free _ e)                  = missingVars e
missingVars (Typed e _)                 = missingVars e
missingVars (Let _ e)                   = missingVars e
missingVars (Case _ _ _)                = 0
missingVars (Or e1 e2)                  = let n1 = missingVars e1
                                              n2 = missingVars e2
                                          in if n1 == n2 then n1 else 0

ground :: Expr -> Bool
ground (Var _)        = True
ground (Lit _)        = True
ground (Comb ct _ es) = ct == ConsCall && all ground es
ground (Free _ _)     = False
ground (Or _ _)       = False
ground (Typed e _)    = ground e
ground (Let _ _)      = False
ground (Case _ _ _)   = False


-- in the expression 
-- let x = e in ...
-- returns true if x is used in e
recursive :: VarIndex -> Expr -> Bool
recursive x (Var y)       = x == y
recursive _ (Lit _)       = False
recursive x (Comb _ _ es) = any (recursive x) es
recursive x (Or e1 e2)    = any (recursive x) [e1,e2]
recursive x (Typed e _)   = recursive x e

recursive x (Free vs e)
 | x `elem` vs = False
 | otherwise   = recursive x e

recursive x (Let vs e)
 | x `elem` map fst vs = False
 | otherwise           = any (recursive x) (e : map snd vs)

recursive x (Case _ e bs) = recursive x e && any recursiveBranch bs
 where recursiveBranch (Branch (LPattern _) be) = recursive x be
       recursiveBranch (Branch (Pattern _ vs) be)
        | x `elem` vs = False
        | otherwise   = recursive x be

nonRecursive :: VarIndex -> Expr -> Bool
nonRecursive x  = not . recursive x


-- implementation of e|_p = w
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


-----------------------------------------------
-- functions for checking variables in an expression.
-----------------------------------------------
max1 :: [Int] -> Int
max1 = foldr max 0

-- variable gaurenteed fresh.
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


hasVar :: VarIndex -> Expr -> Bool
hasVar x e = uses x e > 0

uses :: VarIndex -> Expr -> Int
uses x (Var v)       = if x == v then 1 else 0
uses _ (Lit _)       = 0
uses x (Comb _ _ es) = sum (map (uses x) es)
uses x (Free vs e)   = if x `elem` vs then 0 else uses x e
uses x (Or e1 e2)    = uses x e1 + uses x e2
uses x (Typed e _)   = uses x e
uses x (Let vs e)    = if x `elem` map fst vs then 0 else sum (map (uses x . snd) vs) + uses x e
uses x (Case _ e bs) = uses x e + sum (map useBranch bs)
 where useBranch (Branch (Pattern _ vs) be) = if x `elem` vs then 0 else uses x be
       useBranch (Branch (LPattern _) be)   = uses x be


freeVars :: Expr -> [VarIndex]
freeVars (Var v)       = [v]
freeVars (Lit _)       = []
freeVars (Comb _ _ es) = mergeMap freeVars es
freeVars (Free vs e)   = freeVars e \\- sort vs
freeVars (Or e1 e2)    = freeVars e1 ++- freeVars e2
freeVars (Typed e _)   = freeVars e
freeVars (Let vs e)    = mergeMap freeVars (e : map snd vs) \\- sort (map fst vs)
freeVars (Case _ e bs) = freeVars e ++- mergeMap freeBranch bs
 where freeBranch (Branch (Pattern _ vs) be) = freeVars be \\- vs
       freeBranch (Branch (LPattern _) be)   = freeVars be

-- the variable x is only used once in an execution path.
-- and that context which it is used must evaluate x.
--
-- Right now that means x used as the argument of a case expression,
-- or x is the first argument of apply that is not under any function applications,
-- or x a branch of a case expression.
-- let y = apply x ... is fine
-- f (apply x ...) is not because f might not be strict
--
-- Note: we can actually reuse a variable, but it MUST be in a different case branch.
-- I don't really expect this to happen all that often, but we might as well 
-- allow it.

strict :: VarIndex -> Expr -> Bool
strict _ (Var _)     = False
strict _ (Lit _)     = False
strict _ (Or _ _)    = False
strict x (Typed e _) = strict x e
strict x (Let vs e)  = let es = e : map snd vs
                       in sum (map (uses x) es) == 1 && 
                          length (filter (strict x) es) == 1
strict x (Free _ e)  = strict x e

strict x (Comb _ n es) = isApply && not (any (hasVar x) (tail es))
  where isApply = n == ("Prelude","apply") && length es > 0 && head es == Var x

strict x (Case _ e bs)
 | e == Var x            = not (any (hasVar x) (map branchExpr bs))
 | strictBranch False bs = not (hasVar x e)
 | otherwise             = not (hasVar x e) && any (strict x) (map branchExpr bs)
  where strictBranch found [] = found
        strictBranch found ((Branch _ e'):bs')
         | e' == Var x = strictBranch True bs'
         | otherwise = not (hasVar x e') && strictBranch found bs'


-----------------------------------------------------------------------
--
-- Renaming and substitutions
--
-----------------------------------------------------------------------



-- combinators for building up a substitution
idSub :: VarIndex -> Expr
idSub x = Var x

-- add [x -> e] to a substitution
(@>) :: (Eq a) => (a,b) -> (a -> b) -> (a -> b)
(x,e) @> s = \v -> if x == v then e else s v

-- remove xs from a substitution
(-\) :: (VarIndex -> Expr) -> [VarIndex] -> (VarIndex -> Expr)
s -\ xs = \v -> if v `elem` xs then Var v else s v

-- apply substitution s to expression e
-- The substitution is expected to be defined for all variables in the domain
-- so if (s x) = x if x shouldn't be changed
sub :: (Int -> Expr) -> Expr -> Expr
sub s (Var v)       = s v
sub _ (Lit l)       = Lit l
sub s (Or e1 e2)    = Or (sub s e1) (sub s e2)
sub s (Typed e t)   = Typed (sub s e) t
sub s (Comb t n es) = Comb t n (map (sub s) es)
sub s (Free vs e)   = Free vs (sub (s -\ vs) e)
sub s (Let vs e)    = Let (map (mapSnd (sub s')) vs) (sub s' e)
 where s' = s -\ map fst vs
sub s (Case t e bs) = Case t (sub s e) (map branchSub bs)
 where branchSub (Branch p@(Pattern _ vs) be) = Branch p (sub (s -\ vs) be)
       branchSub (Branch p@(LPattern _ ) be)  = Branch p (sub s be)


-- rename variables in a function
-- We can't use sub for this, because we're replacing all occurences of a variables name
-- and some places (like a Let) don't take an expression.
rename :: VarIndex -> (VarIndex -> VarIndex) -> Expr -> (Expr,VarIndex)
rename n s e = runState (ren s e) n

ren :: (VarIndex -> VarIndex) -> Expr -> Names Expr
ren s (Var v)       = return $ Var (s v)
ren _ (Lit l)       = return $ Lit l
ren s (Free vs e)   = do s' <- extend vs s
                         e' <- ren s' e
                         return $ Free (map s' vs) e'
ren s (Let vs e)    = do s' <- extend (map fst vs) s
                         vs' <- mapM (renPair s') vs
                         e' <- ren s' e
                         return $ Let vs' e'
 where renPair t (v,le) = do le' <- ren t le
                             return (t v, le')
ren s (Or e1 e2)    = do e1' <- ren s e1
                         e2' <- ren s e2
                         return $ Or e1' e2'
ren s (Typed e t)   = do e' <- ren s e
                         return $ Typed e' t
ren s (Comb t n es) = do es' <- mapM (ren s) es
                         return $ Comb t n es'
ren s (Case t e bs) = do e' <- ren s e
                         bs' <- mapM branchRen bs
                         return $ Case t e' bs'
 where
    branchRen (Branch (Pattern n vs) be) = do s' <- extend vs s
                                              be' <- ren s' be
                                              return $ Branch (Pattern n (map s' vs)) be'
    branchRen (Branch (LPattern l) be)   = do be' <- ren s be
                                              return $ Branch (LPattern l) be'

-- add new fresh variables to the substitution
extend :: [Int] -> (Int -> Int) -> Names (Int -> Int)
extend []     s = return s
extend (v:vs) s
 | v == -1   = extend vs s
 | v >= 0    = do n <- fresh
                  extend vs ((v,n) @> s)
 | otherwise = do n <- fresh
                  extend vs ((v,-n) @> s)

-----------------------------------------------------------------------
--
-- Function for primitive operations/unboxing
--
-----------------------------------------------------------------------
-- These aren't a part of the language, I'm just using them for my compiler.
-- specifically for unboxed values.
-- We represent boxed values explicitly with a constructor that can't appear in Curry
-- So, the type Prelude.Int doesn't refer to a primitve type, it referse to a value
-- .int n
-- where n is a primitive type.
-- no one can make a .int constructor (it's syntactically not allowed)

primType :: String -> QName
primType "int" = ("Prelude","Int")
primType "char" = ("Prelude","Char")
primType "float" = ("Prelude","Float")

primCon :: String -> QName
primCon "int" = ("","int")
primCon "char" = ("","char")
primCon "float" = ("","float")

{-
iprimCon :: String -> IQName
iprimCon "int" = ("","int", 0)
iprimCon "char" = ("","char", 0)
iprimCon "float" = ("","float", 0)
-}

litCon :: Literal -> QName
litCon (Intc _)   = ("","int")
litCon (Charc _)  = ("","char")
litCon (Floatc _) = ("","float")

litBranchCon :: [BranchExpr] -> QName
litBranchCon (Branch (LPattern l) _ : _) = litCon l


isLitBranch :: [BranchExpr] -> Bool
isLitBranch (Branch (LPattern _) _ : _) = True
isLitBranch (Branch (Pattern _ _) _ : _) = False

------------------------------------------------------------------------------
-- General utilities:

fork :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
fork f g (x,y) = (f x, g y)

mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst f = fork f id

mapSnd :: (b -> d) -> (a,b) -> (a,d)
mapSnd g  = fork id g

---------------------------------------------------------
-- efficient list functions for sorted lists with no duplicates
---------------------------------------------------------

-- merge a list of sorted lists without duplicates
mergeMap :: (Ord b) => (a -> [b]) -> [a] -> [b]
mergeMap f = merge . map f

-- worst case: O(n*lg(n))
merge :: (Ord a) => [[a]] -> [a]
merge xs = case xs of
                []  -> []
                [x] -> x
                _   -> merge (pair xs)
 where pair ys = case ys of
                      (z1:z2:zs) -> (z1 ++- z2) : pair zs
                      _          -> ys


-- no duplicate union
-- O(n)
(++-) :: (Ord a) => [a] -> [a] -> [a]
[]     ++- ys     = ys
(x:xs) ++- []     = x : xs
(x:xs) ++- (y:ys) = case compare x y of
                         LT -> x : (xs ++- (y:ys))
                         EQ -> x : (xs ++- ys)
                         GT -> y : ((x:xs) ++- ys)

-- difference
-- O(n)
(\\-) :: (Ord a) => [a] -> [a] -> [a]
[]     \\- _      = []
(x:xs) \\- []     = x:xs
(x:xs) \\- (y:ys) = case compare x y of
                         LT -> x : (xs \\- (y:ys))
                         EQ -> xs \\- ys
                         GT -> (x:xs) \\- ys

-- intersection
-- O(n)
(&&-) :: (Ord a) => [a] -> [a] -> [a]
[]     &&- _      = []
(_:_)  &&- []     = []
(x:xs) &&- (y:ys) = case compare x y of
                         LT ->     xs &&- (y:ys)
                         EQ -> x : (xs &&- ys)
                         GT ->     (x:xs) &&- ys

------------------------------------------------------------------------------
--- This gives a monad for creating unique variable names.
--- It's basically the State monad specilized to State Int a.
--- I need to make my own because State is just a type synonym,
--- and you can't make a monad out of that.
------------------------------------------------------------------------------

type Names a = State VarIndex a

fresh :: Names VarIndex
fresh = do v <- get
           put (v+1)
           return v

------------------------------------------------------------------------------
-- This type is an extension of the Writer monad
-- I'm using it for the optimizer, which optimizes by rewriting expressions.
------------------------------------------------------------------------------

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

