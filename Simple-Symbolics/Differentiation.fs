module MathNet.Symbolics.Differentiation

open Core
open MathNet.Symbolics
open Utils

let evalDerivative =
    function
    | IsDerivative(_, IsFunctionExprNameOnly _, _) as f -> f
    | IsDerivative(_, f, dx) -> Calculus.differentiate2 dx f
    | f -> f

let evalAllDerivativeExprs = Structure.recursiveMap evalDerivative >> Expression.simplify true

let D dx e = e |> Calculus.differentiate2 dx |> Expression.simplify true
 
let Dx = evalAllDerivativeExprs

let evalDerivatives = evalAllDerivativeExprs

let newtonsMethodGen simplify iters symbol f x0 =
    let sf = if simplify then Expression.FullSimplify else id 
    let f' = D symbol f
    let rec loop n x0 =
        if n = 0 then x0
        else
            let fx = applyfn f x0
            let fx' = applyfn f' x0
            let x' = (x0 - (fx/fx')) |> sf
            loop (n-1) x'
    loop iters x0

let newtonsMethod = newtonsMethodGen true
 
let chainrule dx f g u x =  
    diff u (f u) * diff dx (g x)
    |> replaceSymbol (g x) u