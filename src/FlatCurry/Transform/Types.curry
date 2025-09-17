------------------------------------------------------------------------------
-- | Author : Michael Hanus, Steven Libby
--   Version: September 2025
--
-- Definition of types used to specify transformations on FlatCurry programs.
------------------------------------------------------------------------------

module FlatCurry.Transform.Types (
  -- * Data types for expression transformations
  Path, Step, ExprTransformation, ExprTransformationDet,
  -- * Operations to lift simple transformations to general ones
  makeT, makeTDet,
  -- * Compose deterministic transformations
  (<?>), combine
)
 where

import FlatCurry.Types

-- | A path to some subepxression is represented by a list of integers.
type Path = [Int]

-- | A transformation step consists of a string, a path, and an expression.
type Step = (String,Path,Expr)

-- | An expression transformation is a (possibly non-deterministic) operation
--   which takes a pair consisting of a fresh variable index and the position
--   of the expression in the right-hand side
--   and a FlatCurry expression and returns a transformed expression,
--   the name of the applied transformation (just for debugging),
--   and the number of new variables used in the transformation,
type ExprTransformation = (VarIndex, Path) -> Expr -> (Expr,String,Int)

-- | An deterministic expression transformation is an totally defined operation
--   which takes a pair consisting of a fresh variable index and the position
--   of the expression in the right-hand side
--   and a FlatCurry expression and returns a `Maybe` value.
--   The result is `Nothing` if the transformation is not applicable,
--   otherwise the result consists of the transformed expression,
--   the name of the applied transformation (for debugging),
--   and the number of new variables used in the transformation,
type ExprTransformationDet = (VarIndex, Path) -> Expr -> Maybe (Expr,String,Int)

------------------------------------------------------------------------------

-- | Lift a simple transformation on expressions to a general
--   expression transformation (of type `ExprTransformation`)
--   where the name of the transformation is provided as the first argument.
makeT :: String -> (Expr -> Expr) -> ExprTransformation
makeT name f = \_ e -> (f e,name,0)

-- | Lift a simple deterministic transformation on expressions to a general
--   deterministic expression transformation (of type `ExprTransformationDet`)
--   where the name of the transformation is provided as the first argument.
makeTDet :: String -> (Expr -> Maybe Expr) -> ExprTransformationDet
makeTDet name f = \_ e -> do e' <- f e
                             Just (e',name,0)

-- | Parallel composition of two deterministic expression transformations
--   where the second transformation is used if the first is not applicable.
(<?>) :: ExprTransformationDet -> ExprTransformationDet -> ExprTransformationDet
t1 <?> t2 = \env e -> case t1 env e of
                           Nothing -> t2 env e
                           Just e' -> Just e'

-- | Parallel composition of a sequence of deterministic expression
--   transformations.
combine :: [ExprTransformationDet] -> ExprTransformationDet
combine = foldr (<?>) (\_ _ -> Nothing)

------------------------------------------------------------------------------
