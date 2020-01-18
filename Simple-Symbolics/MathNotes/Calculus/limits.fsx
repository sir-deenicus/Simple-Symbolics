#load @"C:\Users\cybernetic\Jupyter-Notebooks\maths.fsx"

open MathNet.Numerics
open Prelude.Common
open System
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Operators
open MathNet.Symbolics.Utils
open XPlot.Plotly
open MathNet.Symbolics.Differentiation
open Maths
open MathNet.Symbolics.LinearAlgebra

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

let summation var start stop fx = FunctionN(SumOver, [fx;var;start;V"="; stop])

let (|Summation|_|) input =
     match input with
     | FunctionN(SumOver, [fx;var;start;_; stop]) -> Some(fx,var,start, stop)
     | _ -> None

let extractSumConstants = function
    | Summation(p,v,start,stop) ->
         extractNonVariables v (summation v start stop) p
    | x -> x

let expandSummation = function
    | Summation(Sum _ as s,v,start,stop) ->
         expandSumsOrProducts (summation v start stop) s
    | x -> x


let simplifySums =
    function
    | Summation(n, _, start, stop) when Expression.isNumber n && start = 1Q ->
        n * stop
    | Summation((Identifier _ as x), var, start, stop)
        when start = 1Q && x <> var ->
        x * stop
    | Summation(Identifier _ as x, var, start, n) when start = 1Q && x = var ->
        (Product [ n; n + 1 ]) / 2
    | Summation(Power(Identifier _ as x, p), var, start, n) as expr
        when start = 1Q && x = var ->
        if p = 2Q then (Product [ n; n + 1; 2 * n + 1 ]) / 6
        elif p = 3Q then ((Product [ n; n + 1 ]) / 2) ** 2
        else expr
    | Summation(Product [d;k], var, start, n)
    | Summation(Product [k;d], var, start, n)
        when (start = 0Q || start = 1Q) && k = var ->
        (n+1) * (n * d)/2
    | Summation(Sum [a; Product [d;k]], var, start, n)
    | Summation(Sum [a; Product [k;d]], var, start, n)
        when start = 1Q && k = var ->
        n * (2 * a + (n+1) * d)/2
    | Summation(Sum [a; Product [d;k]], var, start, n)
    | Summation(Sum [a; Product [k;d]], var, start, n)
        when start = 0Q && k = var ->
        (n+1) * (2 * a + n * d)/2
    | Summation(Power(r,k), var, start, n)
        when start = 0Q && k = var && not(isInfinity n) -> ((1-r**(n+1))/(1-r))
    | Summation(Product [Power(r,k); a], var, start, n)
    | Summation(Product [a; Power(r,k)], var, start, n)
        when start = 0Q && k = var && not(isInfinity n) ->
        a * ((1-r**(n+1))/(1-r))
    | x -> x

let simplifyInfiniteSumOfPowers = function
    | Summation(Power(r,k), var, start, n)
        when start = 0Q && k = var && n = infinity -> 1/(1-r)
    | Summation(Product [Power(r,k); a], var, start, n)
    | Summation(Product [a; Power(r,k)], var, start, n)
        when start = 0Q && k = var && n = infinity ->
        a * (1/(1-r))
    | x -> x

PiSigma.Σ(3*a*i**3Q ,1Q,n) |> extractSumConstants |> Structure.recursiveMap simplifySums

PiSigma.Σ(3*a*k**3Q ,k,1Q,n) |> extractSumConstants//|> Structure.recursiveMap simplifySums

PiSigma.Σ(k ,k,1Q,n)  |> simplifySums

let mapList f =
    function
    | Sum l -> Sum(List.map f l)
    | Product l -> Product(List.map f l)
    | x -> x

let i4 = PiSigma (PiSigma.Σ(k**4,k,0Q, n))
[for v in 1N..7N -> i4.Evaluate([n, v]) |> mapList (Expression.Simplify  ) ]

i4.Evaluate([n, 9N]) |> mapList (Expression.Simplify )

(n+1)**4

4 * PiSigma.Σ( (k)**3 ,k,0Q,n) |> Structure.recursiveMap simplifySums

Algebraic.expand ((n+1)**3-1)
PiSigma.Σ( (k+1)**4 ,k,1Q,n) |> Structure.recursiveMap Algebraic.expand |> expandSummation |> Structure.recursiveMap extractSumConstants |> fun x -> x - PiSigma.Σ( (k)**4 ,k,1Q,n) - 4 * PiSigma.Σ( (k)**3 ,k,1Q,n) |> Structure.recursiveMap simplifySums |> fun x -> ((n+1)**4 - x - 1)/ 4 |> Expression.FullSimplify


let isSummation = function | Summation _ -> true | _ -> false

[
Equation.ApplyToRight (Structure.recursiveMapFilter isSummation (Structure.applyInFunction Algebraic.expand))
Equation.ApplyToRight (Structure.recursiveMap expandSummation)
Equation.ApplyToRight (Structure.recursiveMap extractSumConstants)  ]
|> List.map Op
|> equationTrace (PiSigma.Σ( k**5 ,k,1Q,n) <=> PiSigma.Σ( (k+1)**5 ,k,1Q,n) - (n+1)**5)

((Product [ n; n + 1; 2 * n + 1 ]) / 6)|> Algebraic.expand  |> Solving.factorizedPolynomial n
((Product [ n; n + 1 ]) / 2) ** 2 |> Algebraic.expand// |> Solving.factorizedPolynomial n
PiSigma.Σ( d * k ,k,0Q,n)  |> simplifySums |> replaceSymbol 1Q d
PiSigma.Σ( d * k ,k,1Q,n)  |> simplifySums  |> replaceSymbols [ a,0Q; d,1Q ]  |> Expression.Simplify

PiSigma.Σ(1 + 3 * k ,k,1Q,10Q)  |> simplifySums //|> Expression.Simplify

PiSigma.Σ(1 + 3 * k ,k,0Q,10Q)  |> simplifySums// |> Expression.Simplify
PiSigma.Σ(2 *exp (k* -t) ,k,0Q,3Q)   |> Structure.recursiveMap Exponents.replaceExpWithE |> Structure.recursiveMap powerRuleSwapped |> simplifySums |> Expression.evaluateFloat [t, 3.]

let powerRuleRev dohold = function
    | Power(a,Product[Number _ as n;x;y]) ->
        let res = a**(n*x)
        if dohold then (hold res)**y else res**y
    | Power(a,Product[x;y]) ->
        let res = a**x
        if dohold then (hold res)**y else res**y
    | x -> x

let powerRuleRevSwapped dohold = function
    | Power(a,Product[Number _ as n;x;y]) ->
        let res = a**(n*y)
        if dohold then (hold res)**x else res**x
    | Power(a,Product[x;y]) ->
        let res = a**y
        if dohold then (hold res)**x else res**x
    | x -> x


[Rational.applyToNumerator (powerRuleRevSwapped true) >> Expression.Simplify;
 Rational.applyToDenominator Algebraic.expand]
|> List.map Op
|> expressionTrace (e** -b/(1 - e** -b))


PiSigma.Σ(a *exp (k* -b) ,k,0Q,infinity) |> Structure.recursiveMap Exponents.replaceExpWithE|> replaceSymbol 1Q a

PiSigma.Σ( exp (k* -b) ,k,0Q,infinity)   |> Structure.recursiveMap Exponents.replaceExpWithE |> Structure.recursiveMap powerRule  |> simplifyInfiniteSumOfPowers  |> replaceSymbol 1Q a  |> Expression.Simplify

PiSigma.Σ( p  ,k,0Q,n) |> simplifySums



PiSigma.Σ(10Q * 3Q ** k ,k,0Q,3Q)  |> simplifySums

PiSigma.Σ((3-2*i)**2Q ,1Q,n) |> Structure.recursiveMap Algebraic.expand |> expandSummation |> Structure.recursiveMap extractSumConstants |> Structure.recursiveMap simplifySums |> Expression.FullSimplify

PiSigma.Σ(a*n,1Q,n) |> extractSumConstants |> Structure.recursiveMap simplifySums

PiSigma.Σ(c,1Q,n) |>simplifySums
PiSigma.Σ(1Q,1Q,n) |> simplifySums


let (|IsLimit|_|) input =
     match input with
     | FunctionN(Limit, [var;lim;x]) -> Some(var,lim,x)
     | _ -> None

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


PiSigma.Σ(ln(1 - 1/(n+1)**2),n,1Q,infinity)

limit z 1Q ((6 - 3 * z + 10*z**2)/(-2*z**4 + 7*z**3 + 1))

evalLimit (limit z 1Q ((6 - 3 * z + 10*z**2)/(-2*z**4 + 7*z**3 + 1))) |> Expression.Simplify

let (|Binomial|_|) input =
     match input with
     | FunctionN(Choose, [n;k]) -> Some(n,k)
     | _ -> None

let rec rfun r (v:Expression) n = if n = 0 then v else rfun r (Expression.FullSimplify(v + v * r)) (n-1)

let binomialTheorem = function
    | Summation
        (Product
           [Power (b,k2);
            Power (a, Sum [Product [Number _ as neg1; k]; n]);
            Binomial(n2,k3)], k4, start, n3)
    | Summation
        (Product
           [Power (a, Sum [Product [Number _ as neg1; k]; n]);
            Power (b,k2); Binomial(n2,k3)], k4, start, n3)
        when k = k2 && k2 = k3 && k3 = k4 &&
             neg1 = -1Q && start = 0Q &&
             n = n2 && n2 = n3 -> (a + b)**n
    | Summation(Product [ Power(r,k2); Binomial(n,k)], k3, start, n2)
        when k = k2 && k2 = k3 && start = 0Q && n = n2 -> (1+r)**n
    | Summation(Binomial(n,k), k2, start, n2)
        when k = k2 && start = 0Q && n = n2 -> 2Q ** n
    | Summation(Product [ k2; Binomial(n,k)], k3, start, n2)
        when k = k2 && k2 = k3 && start = 0Q && n = n2 -> n * 2Q**(n-1)
    | x -> x

PiSigma.Σ (choose n k , k, 0Q,n) |> binomialTheorem

PiSigma.Σ (choose (n) k  * y**(n-k) * x ** k, k, 0Q,n)|> binomialTheorem

let S1 = Vector [a ;             (a + d) ;       V"...";  (a + (n-2)*d) ; (a + (n-1)*d)]
let S2 = Vector [(a + (n-1)*d) ; (a + (n-2)*d) ; V"...."; (a + d);         a]

let S1 = Vector [(a + d);      (a + 2 * d) ;   V"...";  (a + (n-1)*d) ;  (a + (n)*d)]
let S2 = Vector [(a + (n)*d) ; (a + (n-1)*d) ; V"...."; (a + 2 * d)  ; (a + d)]

PiSigma.Σ (a+k *d, k,1Q,2Q) |> PiSigma.Evaluate

S1
S2

let cc = (S1 |> Vector.toList |> List.sum) + (S2 |> Vector.toList |> List.sum) |> Expression.FullSimplify //|> Structure.filter (symbolString >> Strings.strcontains "..." >> not) |> Algebraic.consolidateSums2


let consolidateSums chooser = function
    | Sum l ->
        let exprlist = List.toArray l

        let divides =
            [| for i in 0..exprlist.Length - 2 do
                   for j in i + 1..exprlist.Length - 1 do
                       let d = (exprlist.[i] / exprlist.[j])

                       let xr =
                           exprlist.[i] / Rational.numerator d
                           |> abs
                           |> Expression.cancelAbs
                       if xr <> 1Q then yield xr |]
            |> Hashset
            |> Seq.toArray

        let divisor = chooser divides

        let divisibles, undivisible =
            exprlist
            |> Array.groupBy (fun x -> Rational.denominator (x / divisor) = 1Q)
            |> Array.partition fst

        let divided =
            divisibles.[0]
            |> snd
            |> Array.map (fun x -> x / divisor)
            |> List.ofArray
            |> Sum

        divisor * divided + Sum (List.ofArray (snd undivisible.[0]))
    | x -> x

(S1 + S2) |> Vector.map (Expression.FullSimplify) |> Vector.toList |> List.groupBy id |> List.map fst

(S1 + S2) |> Vector.map (Expression.FullSimplify) |> Vector.toList |> List.groupBy id |> List.map fst |> List.head |> fun x -> n*x/2 |> Structure.recursiveMap (consolidateSums (Array.minBy width))

PiSigma.Σ (choose (n) k  * r **k, k, 0Q,n)  |> binomialTheorem
PiSigma.Σ (choose (T) n * a * r **n, n, 0Q,T) |> extractSumConstants |> Structure.recursiveMap binomialTheorem  <=> R
|> Solving.reArrangeEquation r //|> Expression.FullSimplify
rfun r (a) 5
PiSigma.Σ (choose (T) n * a * r **n, n, 0Q,T) |> extractSumConstants |> Structure.recursiveMap binomialTheorem |> replaceSymbols [r, -1/10Q;a,1Q;  T,100Q]|> Expression.Simplify |> Expression.toFloat
