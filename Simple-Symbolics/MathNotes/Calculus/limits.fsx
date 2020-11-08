
#load @"C:\Users\cybernetic\Jupyter-Notebooks\maths.fsx"

open MathNet.Numerics
open Prelude.Common
open System
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Operators
open MathNet.Symbolics.Utils
open XPlot.Plotly
open MathNet.Symbolics.Differentiation
open Maths
open MathNet.Symbolics.LinearAlgebra
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Summation
open MathNet.Symbolics.Units

setLatex()

#r "netstandard"
#r @"C:\Users\cybernetic\source\repos\Prelude\Prelude\bin\Release\net47\prelude.dll"
#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\bin\Release\net47"
#I @"C:\Users\cybernetic\.nuget\packages\"
#r @"fsharp.data\3.3.2\lib\netstandard2.0\FSharp.Data.DesignTime.dll"
#r @"fsharp.data\3.3.2\lib\netstandard2.0\FSharp.Data.dll"
#r @"MathNet.Numerics.dll"
#r @"MathNet.Numerics.Fsharp.dll"
#r @"MathNet.Symbolic.Ext.dll"
#r "Simple-Symbolics.dll"
open MathNet.Numerics
open Prelude.Common
open System
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Operators
open MathNet.Symbolics.Utils
open MathNet.Symbolics.Differentiation
open MathNet.Symbolics.LinearAlgebra
open MathNet.Symbolics.Solving
open MathNet.Symbolics.Units

open NumberProperties
open Expression
 
setLatex()
 
(t - sqrt (3 * t + 4)) / (4 - t)
|> Rational.rationalizeNumeratorWithConjugate
|> Structure.recursiveMapFilter
       (fun x -> Polynomial.isPolynomial t x && Polynomial.degree t x
                                                |> Expression.toInt > 1)
       (factorizedPolynomial t)
|> Structure.recursiveMapFilter ((=) (4 - t)) negateId
|> Rational.rationalize
|> replaceSymbol 4Q t
|> Expression.FullSimplify


(sqrt(3*x**2 + 6)/(5-2*x))|> Rational.applyToNumerator (Structure.applyInFunction (fun v -> x **2 * Algebraic.expand(v / x**2)) >> Expression.Simplify )

(sqrt(3*x**2 + 6)/(5-2*x))|> Rational.applyToNumerator (Structure.applyInFunction (fun v -> x **2 * Algebraic.expand(v / x**2)) >> Expression.Simplify >> negate )

let expandSumsOrProducts f = function
    | Sum l -> l |> List.map f |> Sum
    | Product l -> l |> List.map f |> Product
    | x -> x

let extractConstant f = function
    | Product (c::l) when Expression.isNumber c ->
        match l with
        | [] -> c
        | [x] -> c * f x
        | _ -> c * f (Product l)
    | x -> x

let extractNonVariables x f = function
    | Product l ->
        let hasvar, consts = List.partition (containsVar x) l
        let consts' =
            match consts with
            | [] -> 1Q
            | [ x ] -> x
            | _ -> Product consts

        let vars =
            match hasvar with
            | [] -> 1Q
            | [ x ] -> x
            | _ -> Product hasvar
        consts' * f vars
    | v -> if containsVar x v then f v else v * f 1Q



PiSigma.Σ((3-2*i)**2Q ,1Q,n) |> Structure.recursiveMap Algebraic.expand |> expandSummation |> Structure.recursiveMap extractSumConstants |> Structure.recursiveMap simplifySums |> Expression.FullSimplify


let (|IsLimit|_|) input =
     match input with
     | FunctionN(Limit, [var;lim;x]) -> Some(var,lim,x)
     | _ -> None

let evalLimit = function
     | IsLimit(var,lim,x) ->
         replaceSymbol lim var x
     | x -> x

let cLimit = function
    | IsLimit(var,lim,Product (c::l)) when Expression.isNumber c -> c * limit var lim (Product l)
    | x -> x

let sLimit = function
    | IsLimit(var,lim,Sum l) ->
        l |> List.map (fun x -> limit var lim x) |> Sum
    | IsLimit(var,lim,(Product _ as p)) as f ->
        let den = Rational.denominator p
        if den <> 1Q then
            let num = Rational.numerator p
            (limit var lim num)/(limit var lim den)
        else f

    | IsLimit(var,lim,Product l) ->
        l |> List.map (fun x -> limit var lim x) |> Product
    | x -> x


let simpinf = function Power(x, n) when n = infinity && Structure.exists hasNegatives x -> undefined | x -> x

((-a/b)**n)|> Exponents.expandRationalPower |> replaceSymbol infinity n |> Expression.Simplify |> Algebraic.expand |> Structure.toList |> List.map (Expression.FullSimplify)
simpinf ((-a/b)**infinity)

(2/3Q)**n |> Exponents.expandRationalPower |> Expression.expandSumsOrProducts (limit n infinity)// |> recmap evalLimit// |> Structure.toList |> List.map (Expression.FullSimplify >> simpinf)

let var = x
let lim = a

sLimit (limit x a (q + y * fx x)) |> Structure.recursiveMap sLimit

let pv = (fx x/ funcx "g" x)

limit x a (fx x/ funcx "g" x) |> sLimit

let evalLimit = function
    | IsLimit(var,lim,x) ->
        replaceSymbol lim var x
    | x -> x


evalLimit (limit x -2Q (3* x **2 + 5 * x - 9)) |> Expression.Simplify


PiSigma.Σ(1/k,k,1Q,n) |> extractSumConstants//|> Structure.recursiveMap simplifySums |> Expression.Simplify
limit n infinity (PiSigma.Σ(1/n - k**2/n**3,k,1Q,n))

PiSigma.Σ(1/n - k**2/n**3,k,1Q,n) |> expandSummation |> Structure.recursiveMap extractSumConstants |> Structure.recursiveMap simplifySums |> Expression.FullSimplify



limit z 1Q ((6 - 3 * z + 10*z**2)/(-2*z**4 + 7*z**3 + 1))

evalLimit (limit z 1Q ((6 - 3 * z + 10*z**2)/(-2*z**4 + 7*z**3 + 1))) |> Expression.Simplify
