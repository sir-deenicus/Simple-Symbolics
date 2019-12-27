module MathNet.Symbolics.Differentiation

open Core
open MathNet.Symbolics
open Utils

let evalDerivative =
    function
    | IsDerivative(f, dx) -> Calculus.differentiate2 dx f
    | f -> f

let evalAllDerivativeExprs = Structure.recursiveMap evalDerivative >> Algebraic.simplify true

let D dx e = e |> Calculus.differentiate2 dx |> Algebraic.simplify true
 
let Dx = evalAllDerivativeExprs

let derivs = evalAllDerivativeExprs

let newtonsMethod simplify n symbol f x0 =
    let sf = if simplify then Expression.FullSimplify else id
    let f' = D symbol f
    let rec loop n x0 =
        if n = 0 then x0
        else
            let x' = (x0 - (Func.Apply(f, x0)/Func.Apply(f',x0))) |> sf
            loop (n-1) x'
    loop n x0