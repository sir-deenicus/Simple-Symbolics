module MathNet.Symbolics.Differentiation

open Core
open MathNet.Symbolics

let grad x = FunctionN(Gradient, [x])
let gradn var x = FunctionN(Gradient, [x;var] )
let diff dx x = FunctionN(Derivative, [x;dx])
let pdiff dx x = FunctionN(PartialDerivative, [x;dx])

let (|IsDerivative|_|) = function
     | FunctionN(PartialDerivative, [ x; dx ])
     | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
     | _ -> None 

let evalDerivative =
    function
    | IsDerivative(f, dx) -> Calculus.differentiate dx f
    | f -> f

let evalDerivs = Structure.recursiveMap evalDerivative >> Algebraic.simplify true

let D = evalDerivs >> Calculus.differentiate
