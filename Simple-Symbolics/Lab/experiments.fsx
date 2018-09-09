#load "core.fsx"

open MathNet.Symbolics
open Core.Vars

Polynomial.factorSquareFree x (x ** 3 + 2 * x) |> Infix.format

Polynomial.variables (x**3 + 2 * x)

Algebraic.expand ((x+1) **4 / (4)) |> Infix.format

Polynomial.factorSquareFree b (a ** 2 + 2 * a * b + b ** 2) |>  (Infix.format)


