module MathNet.Symbolics.Differentiation

open Core
open MathNet.Symbolics
open Utils
open NumberProperties
open Prelude.Common

[<RequireQualifiedAccess>]
type EvalMethod = 
    | None 
    | Simplify
    | Numeric

///Given an input expression that's a Leibniz notation expression of the derivative of a function, calculates its derivative.
let evalDerivative =
    function
    | IsDerivative(_, f, dx) -> Calculus.differentiate2 dx f
    | IsNthDerivative(_, f, dx, AsInteger n) -> repeat (int n) (Calculus.differentiate2 dx) f
    | f -> f

///Recursively evaluates all derivative notation expressions in expression. see also Dx shorthand.
let evalDerivativeExprs = Structure.recursiveMap evalDerivative >> Expression.simplify

///calculates (partial) derivative of given expression, compare with diff which wraps an expression in leibniz differentiation notation
let D dx e = e |> Calculus.differentiate2 dx |> Expression.simplify
 
///short-hand for evalDerivativeExprs which recursively evaluates all derivative notation expressions in expression.
let Dx = evalDerivativeExprs
  
/// <summary>
/// Newton's method is an iterative method for finding the roots of a differentiable function f, which are the values of x such that f(x) = 0. 
/// The method starts with a guess x0 for a root of f, and repeatedly improves the guess by Newton's method formula: x_{n+1} = x_n - f(x_n)/f'(x_n), 
/// where f' is the derivative of f. The function newtonsMethodAux implements Newton's method for finding the roots of a function f. 
/// </summary>
/// <param name="evalMethod">The method used to evaluate the function. None means no evaluation, Simplify means full simplification, Numeric means numeric evaluation.</param>
/// <param name="symbol">The symbol with respect to which the derivative is taken.</param>
/// <param name="iters">The number of iterations to perform.</param>
/// <param name="f">The function to find the roots of.</param>
/// <param name="x0">The initial guess for the root.</param>
/// <returns>The root of the function f.</returns>
let newtonsMethodAux evalMethod symbol iters f x0 =
    let eval =
        match evalMethod with
        | EvalMethod.None -> id
        | EvalMethod.Simplify -> Expression.fullSimplify
        | EvalMethod.Numeric -> Expression.toFloat >> Option.get >> ofFloat
         
    let fx = toFunc f 
    let fx' = toFunc (D symbol f) 

    let rec loop n x =
        if n = 0 then x
        else 
            eval(x - (fx x / fx' x))  
            |> loop (n - 1) 
    loop iters x0

/// <summary>
/// Newton's method is an iterative method for finding the roots of a differentiable function f, which are the values of x such that f(x) = 0. 
/// The method starts with a guess x0 for a root of f, and repeatedly improves the guess by Newton's method formula: x_{n+1} = x_n - f(x_n)/f'(x_n), 
/// where f' is the derivative of f. The function newtonsMethod implements Newton's method for finding the roots of a function f in numeric (and not symbolic) mode. 
/// </summary>
/// <param name="symbol">The symbol with respect to which the derivative is taken.</param>
/// <param name="iters">The number of iterations to perform.</param>
/// <param name="f">The function to find the roots of.</param>
/// <param name="x0">The initial guess for the root.</param>
/// <returns>The root of the function f.</returns>
let newtonsMethod symbol iters f x0 = newtonsMethodAux EvalMethod.Numeric symbol iters f x0

/// <summary>
/// Computes the derivative of a composition of two functions using the chain rule.
/// </summary>
/// <param name="dx">The variable with respect to which the derivative is taken.</param>
/// <param name="f">The outer function.</param>
/// <param name="g">The inner function.</param>
/// <returns>A function that represents the derivative of the composition of f and g.</returns>
let chainrule dx f g =  
    let u = !"u_{chain.sub}"
    fun x ->
        diff u (f u) * diff dx (g x)
        |> replaceSymbolWith (g x) u