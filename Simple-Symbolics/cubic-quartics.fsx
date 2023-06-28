#r @"bin\Debug\net5\Simple-Symbolics.dll"

open MathNet.Symbolics.Complex
open MathNet.Numerics.FindRoots
open System  

let cubicSolve (coeffs: Expression[]) =
    let coeffs =
        [| for c in coeffs do
               match Expression.toFloat c with
               | Some c -> c
               | None -> () |]

    let a = coeffs[3]
    let b = coeffs[2]
    let c = coeffs[1]
    let d = coeffs[0]
 
    let struct(r1,r2,r3) = MathNet.Numerics.FindRoots.Cubic(d, c, b, a)
    Array.map Complex.ofNumericsComplex [|r1;r2;r3|]
     
//cubic solver lightly adjusted from https://github.com/BaseMax/CubicEquationCalculator/blob/main/cubic.js which itself heavily derives from undisclosed sources.

let quarticSolve0 (coeffs: Expression[]) =
    let coeffs =
        [| for c in coeffs do
               match toFloat c with
               | Some c -> c
               | None -> () |]

    if coeffs.Length <> 5 then
        [||]
    else
        let a = coeffs[4]
        let b = coeffs[3]
        let c = coeffs[2]
        let d = coeffs[1]
        let e = coeffs[0]

        let D0 = c * c - 3.0 * b * d + 12.0 * a * e

        let D1 =
            2.0 * c * c * c - 9.0 * b * c * d + 27.0 * b * b * e + 27.0 * a * d * d
            - 72.0 * a * c * e

        let p = (8.0 * a * c - 3.0 * b * b) / (8.0 * a * a)
        let q = (b * b * b - 4.0 * a * b * c + 8.0 * a * a * d) / (8.0 * a * a * a)

        let Q =
            Numerics.Complex.Pow(
                (D1 + Numerics.Complex.Sqrt(D1 * D1 - Numerics.Complex(4.0, 0.) * D0 * D0 * D0))
                / 2.0,
                1.0 / 3.0
            )

        let S = Numerics.Complex.Sqrt(-2.0 * p / 3.0 + (Q + D0 / Q) / (3.0 * a)) / 2.0
        let u = Numerics.Complex.Sqrt(-4.0 * S * S - 2.0 * p + q / S) / 2.0
        let v = Numerics.Complex.Sqrt(-4.0 * S * S - 2.0 * p - q / S) / 2.0
        let x1 = -b / (4.0 * a) - S + u
        let x2 = -b / (4.0 * a) - S - u
        let x3 = -b / (4.0 * a) + S + v
        let x4 = -b / (4.0 * a) + S - v
        [| x1; x2; x3; x4 |] |> Array.map Complex.ofNumericsComplex
 
2 * x** 3Q + 3 * x ** 2Q + 4 * x + 5
|> Polynomial.coefficients x
//|> Solving.cubicSolve
|> Solving.cubicSolve
|> List.map Expression.simplify

|> Array.map Complex.toExpression
//|> Array.map (Complex.apply (Expression.simplify >> Trigonometric.simplify >> rm Algebraic.consolidateSums ))

//quartic 1. -7 5. 31. -30.
  
x ** 4Q - 7Q * x ** 3Q + 5Q * x ** 2Q + 31Q * x - 30Q
|> Polynomial.coefficients x
|> quarticSolve
|> Array.map (Complex.apply (Approximation.round 3 >> Expression.simplify))
|> Array.map Complex.toExpression