#load "solving.fsx"
open System.Collections.Generic

open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics
open MathNet.Symbolics
open Solving

/////////////// 

module Logarithms =
  let expand = function 
   | Function(Ln, Product l) -> Sum(List.map (function Power(x, n) when n = -1Q -> ln (-x) | x -> ln x) l)
   | f -> f
  let powerContract = function 
     | Power(x, n) -> Choice1Of2 (x,n)
     | f -> Choice2Of2 f
  let contract = function 
    | Sum l -> 
       let logs, rest = 
           List.partition (function 
             | Function(Ln,_) -> true 
             | Product[n;Function(Ln, _)] when n = -1Q -> true
             | _ -> false) l
       let logs' = 
           logs |> List.map (function 
                     | Product[n;Function(Ln, x)] when n = -1Q -> 1/x 
                     | Function(Ln, x) -> x 
                     | _-> failwith "never")
       ln(Product logs') + Sum rest
    | f -> f

Logarithms.contract (ln a - ln b)

let sigma2, sigma1 = Operators.symbol "\sigma_2",Operators.symbol "\sigma_1"

let zz = (1/2Q * ln(2 * pi * sigma2 ** 2) + -1/2Q * (1 + ln(2 * pi * sigma1 ** 2)) )

Logarithms.contract (1/2Q * ln(2 * pi * sigma2 ** 2) + -1/2Q * (1 + ln(2 * pi * sigma1 ** 2)) )

Structure.collectAll (function Function (Ln, x) -> Some x | _ -> None) zz

zz |>  Algebraic.expand

zz |> findVariablesOfExpression

Structure.collectNumberValues zz

 
/////////////////////

let p1 = x ** 3 - 4 * x ** 2 - 7 * x + 10

let p1' = x ** 3 - 4 * x ** 2 - 7 * x  

let p2 = x ** 3 + 6 * x ** 2 + 5 * x - 12

let p3 = x ** 5 - 4*x**4 - 7 * x**3 + 14 * x **2 - 44 * x + 120

let p4 = x ** 3 + x - 1
 
let p5 = 3 * x ** 3 - 5 * x ** 2 + 5 * x - 2

 
let ac,bc = quadraticSolve (x**2 + 53 * x + 12)

pairmap (Infix.format) (ac,bc) 

quadraticSolve (a * x**2 + b) //|> pairmap Infix.format

let rec tryFactorizePolynomial x fx =
    let constant = Polynomial.coefficient x 0 fx 
    let deg = Polynomial.degree x fx
    if constant = 0Q && deg.ToInt() < 2 then [], []
    elif deg.ToInt() = 1 then [-constant], []
    elif constant = 0Q then 
      let fx', _  = Polynomial.divide x fx x
      let sols, eq = tryFactorizePolynomial x fx'  
      0Q::sols, fx'::eq
    else
      let factors = factorsExpr (abs constant)
      let r,s =
         List.unzip
           [for f in (List.map ((*) -1) factors) @ factors do
                  let n = f.ToFloat()  
                  let value = Evaluate.evaluate (Map ["x", FloatingPoint.Real n]) fx
                  if value.RealValue = 0. then 
                      yield (f, Polynomial.divide x fx (x - f) |> fst) ] 
      let sols, eq = List.map (tryFactorizePolynomial x) s |> List.unzip
      r @ List.concat sols |> HashSet |> Seq.toList, s @ List.concat eq |> HashSet |> Seq.toList
  
 
tryFactorizePolynomial n (n**3 + 3*n**2 + 2*n)
let res = tryFactorizePolynomial x p5
let mm = Polynomial.divide x p5 3Q |> fst 
//|> pairmap Infix.format
res |> pairmap (List.map Infix.format)
res |> snd |> List.filter (Polynomial.degree x >> ((=) 2Q)) |> List.map (quadraticSolve >> pairmap (Algebraic.simplify true >> Rational.simplify x >> Infix.format))

Structure.substitute 1Q x p5  

Structure.map (function | Identifier (Symbol "x") -> printfn "eg"; 1Q | x -> x) p5
replaceSymbol (2Q/3Q) x p5 |> Rational.simplify x |> Infix.format

 
p5.ToFormattedString()
 