flatcurry-transform
===================

This package provides a framework to support transformations on FlatCurry
programs.
A simple transformation on a FlatCurry expression is an operation
of type

    Expr -> Expr

which can be partially defined and also non-deterministic.
For instance, a transformation to remove type annotations
can be defined by

    unTypeRule :: Expr -> Expr
    unTypeRule (Typed e _) = e

Note that this operation is partially defined since it fails
on non-`Typed` expressions. However, it is a natural representation
of the idea of this transformation.

Similarly, a transformation to remove occurrences of the prelude
operation `?` by replacing them by the choice construct of FlatCurry
can be defined by

    removeQuestionRule :: Expr -> Expr
    removeQuestionRule (Comb FuncCall ("Prelude","?") [e1,e2]) = Or e1 e2

The library `FlatCurry.Transform.Types` defines the type
`ExprTransformation` to support more complex transformations
which might require fresh variables or the subterm position.
The auxiliary operation `makeT` lifts a simple transformation
into such a general transformation where a name must be provided
which is used during debugging. For instance, we can define

    unType :: ExprTransformation
    unType = makeT "UNTYPE" unTypeRule
    
    removeQuestion :: ExprTransformation
    removeQuestion = makeT "REMOVE-?-CAll" removeQuestionRule

The library `FlatCurry.Transform.Exec` defines the operation `transformExpr`
to apply a transformation as long as possible.
If a transformation is non-deterministic, as

    (unType ? removeQuestion)

all possible transformations are applied in an unspecified order.
The examples (see below) contain code snippets showing the
use of the operation `transformExpr`.


Examples
--------

The subdirectory `examples` contains various example transformations
in the programs

- `Transformations.curry` (functional logic transformations as described above)
- `DetTransformations.curry` (deterministic transformations)
