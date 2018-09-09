#load "linear-algebra.fsx"

open MathNet.Symbolics
open Core
open Core.Vars
open ``Linear-algebra``

let vectorScalarDerivative vector scalar = 
    List.map (Calculus.differentiate scalar) vector
 
let scalarVectorDerivative coords functionExpr = 
    List.map (flip Calculus.differentiate functionExpr) coords
 
let vectorVectorDerivative x y = 
    [for yi in y ->
       [for xi in x -> Calculus.differentiate xi yi]]

let jacobian = vectorVectorDerivative

let gradient = scalarVectorDerivative

let f x y = 3Q * x ** 2 * y

Calculus.differentiate y (f x y) |> Calculus.differentiate x
Calculus.differentiate (x**2 + y**2) y**2


gradient [x;y] (f x y)  |> List.map Infix.format

vectorScalarDerivative [1 + x**2;exp (2*x);cos x] (x) |> List.map Infix.format


det2 [[a;b];[c;d]] |> Infix.format

vectorVectorDerivative [r;phi] [r * cos phi; r * sin phi]|> List.map (List.map Infix.format)

vectorVectorDerivative [r;phi] [r * cos phi; r * sin phi] |> det2 |> Trigonometric.simplify |> Infix.format
vectorVectorDerivative [x1;x2;x3] [x1; 5*x3;4*x2**2-2*x3;x3*sin x1] |> List.map (List.map Infix.format)
vectorVectorDerivative  [x;y] [x**2 * y;5*x+sin y] |> List.map (List.map Infix.format)
scalarVectorDerivative [x;y] 
vectorVectorDerivative  [x;y] [x**2 * y;5*x+sin y] |> det2 |> Infix.format

Calculus.differentiate x1 (x1 ** 2)
