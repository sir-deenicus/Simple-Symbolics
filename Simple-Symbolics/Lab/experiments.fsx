#load "core.fsx"

open MathNet.Symbolics
open Core.Vars
open Core

let sq = sqrt 2Q / 2

let a1 = Complex(2Q, 5Q)

let b1 = Complex(3Q, 2Q)

let za = System.Numerics.Complex(2.,5.)
let zb = System.Numerics.Complex(3.,2.)

a1*b1
za * zb
a1 + b1
za + zb
za - zb
a1 - b1

a1 * a1.Conjugate
a1.Magnitude.ToFormattedString()
Evaluate.evaluate Map.empty a1.Magnitude
za.Magnitude

MathNet.Numerics.Complex.conjugate za
za * MathNet.Numerics.Complex.conjugate za
a1.Conjugate 

Infix.format sq

Polynomial.factorSquareFree x (x ** 3 + 2 * x) |> Infix.format

Polynomial.variables (x**3 + 2 * x)

Algebraic.expand ((x+1) **4 / (4)) |> Infix.format

Polynomial.factorSquareFree b (a ** 2 + 2 * a * b + b ** 2) |>  (Infix.format)


