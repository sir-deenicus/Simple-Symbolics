module MathNet.Symbolics.Differentiation

open Core
open MathNet.Symbolics
open Utils
open NumberProperties

[<RequireQualifiedAccess>]
type EvalMethod = 
    | None 
    | Simplify
    | Numeric

///Given an input expression that's a Leibniz notation expression of the derivative of a function, calculates its derivative.
let evalDerivative =
    function
    | IsDerivative(_, IsFunctionExprNameOnly _, _) as f -> f
    | IsDerivative(_, f, dx) -> Calculus.differentiate2 dx f
    | f -> f

///Recursively evaluates all derivative notation expressions in expression. see also Dx shorthand.
let evalDerivativeExprs = Structure.recursiveMap evalDerivative >> Expression.simplify true

///calculates (partial) derivative of given expression, compare with diff which wraps an expression in leibniz differentiation notation
let D dx e = e |> Calculus.differentiate2 dx |> Expression.simplify true
 
///short-hand for evalDerivativeExprs which recursively evaluates all derivative notation expressions in expression.
let Dx = evalDerivativeExprs
  
let newtonsMethodAux evalMethod symbol iters f x0 =
    let eval =
        match evalMethod with
        | EvalMethod.None -> id
        | EvalMethod.Simplify -> Expression.FullSimplify
        | EvalMethod.Numeric -> Expression.toFloat >> Option.get >> ofFloat
         
    let fx = toFunc f 
    let fx' = toFunc (D symbol f) 

    let rec loop n x =
        if n = 0 then x
        else 
            eval(x - (fx x / fx' x))  
            |> loop (n - 1) 
    loop iters x0

let newtonsMethod symbol iters f x0 = newtonsMethodAux EvalMethod.Numeric symbol iters f x0
 
let chainrule dx f g =  
    let u = !"u_{chain.sub}"
    fun x ->
        diff u (f u) * diff dx (g x)
        |> replaceSymbol (g x) u