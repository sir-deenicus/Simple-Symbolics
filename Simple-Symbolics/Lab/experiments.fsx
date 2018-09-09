#load "core.fsx"

open MathNet.Symbolics
open Core.Vars
open Core

let sq = sqrt 2Q / 2

sq.ToFloat()

let a1 = Complex(-2Q, sqrt 5Q)

let b1 = Complex(3Q, 2Q)

let za = System.Numerics.Complex(-2.,System.Math.Sqrt 5.)
let zb = System.Numerics.Complex(3.,2.)

za.Phase
a1.Phase.ToFormattedString()
a1.Phase.ToFloat()

a1*b1
za * zb
a1 + b1
za + zb
za - zb
a1 - b1

5. * za
5Q * a1

Complex(5Q, 7Q) * -5Q  
Complex(5Q, 7Q) * Complex -5Q  


System.Numerics.Complex(5.,7.) * System.Numerics.Complex(-5.,0.)

List.sum [Complex 5Q ; Complex 3Q]

Complex(a, b) * Complex(c, 0Q)
Complex(a, b) * c
a1 * a1.Conjugate
a1.Magnitude.ToFormattedString()
a1.Magnitude.ToFloat()
za.Magnitude

MathNet.Numerics.Complex.conjugate za
za * MathNet.Numerics.Complex.conjugate za
a1.Conjugate 

Infix.format sq

Polynomial.factorSquareFree x (x ** 3 + 2 * x) |> Infix.format

Polynomial.variables (x**3 + 2 * x)

Algebraic.expand ((x+1) **4 / (4)) |> Infix.format

Polynomial.factorSquareFree b (a ** 2 + 2 * a * b + b ** 2) |>  (Infix.format)


