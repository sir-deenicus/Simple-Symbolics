module MathNet.Symbolics.Summation

open MathNet.Numerics
open MathNet.Symbolics
open MathNet.Symbolics.NumberProperties
open MathNet.Symbolics.Core
open Utils
open Operators
open Prelude.Common
open NumberProperties

///Adjusts summation to have a start, stop or var if it does not already
let adjustSummationTo var start stop = function
  | FunctionN (SumOver,[p; v]) ->
       summation v start stop p
  | FunctionN (SumOver,[p]) ->
       summation var start stop p
  | x -> x

let isSummation = function | Summation _ -> true | _ -> false

let extractSumConstants = function
  | FunctionN (SumOver,[p; var]) ->
       Structure.extractNonVariablesAndApplyF var (fun x -> Summations.Σ(x, var)) p
  | Summation(p,v,start,stop) ->
       Structure.extractNonVariablesAndApplyF v (summation v start stop) p
  | x -> x

let expandSummation = function
    | Summation(Sum _ as s,v,start,stop) ->
         Structure.mapRootList (summation v start stop) s
    | x -> x

///merge summations in a sum that have the same parameters, eg Σ x + Σ y to Σ (x+y)
let mergeSummationsInSum =
    let getSummation =
        function
        | Summation(fx, v, s, stop) -> fx, (v, s, stop)
        | _ -> failwith "Unexpected error in getsummation"
    function
    | Sum es ->
        let sums, nonsum = //split to sums and non-sums
            List.partition (function
                | Summation _ -> true
                | _ -> false) es
        Sum //group by summation parameters
            [ for ((v, s, stop), l) in List.groupBy (getSummation >> snd) sums ->
                Σ v s stop (Sum (List.map (getSummation >> fst) l)) ] //need to extract inside content of summation
        + Sum(nonsum)
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
        when (start = 0Q || start = 1Q) && k = var && not(isInfinity n) ->
        (n+1) * (n * d)/2
    | Summation(Sum [a; Product [d;k]], var, start, n)
    | Summation(Sum [a; Product [k;d]], var, start, n)
        when start = 1Q && k = var && not(isInfinity n) ->
        n * (2 * a + (n+1) * d)/2
    | Summation(Sum [a; Product [d;k]], var, start, n)
    | Summation(Sum [a; Product [k;d]], var, start, n)
        when start = 0Q && k = var && not(isInfinity n) ->
        (n+1) * (2 * a + n * d)/2
    | Summation(Power(r,k), var, start, n)
        when start = 0Q && k = var && not(isInfinity n) -> ((1-r**(n+1))/(1-r))
    | Summation(Product [Power(r,k); a], var, start, n)
    | Summation(Product [a; Power(r,k)], var, start, n)
        when start = 0Q && k = var && not(isInfinity n) ->
        a * ((1-r**(n+1))/(1-r))
    | Summation(f, var, start, stop)
        when start = 1Q && not(containsVar var f) ->
        f * stop
    | x -> x

/// condition: r <= 1, r > 0
let simplifyGeometricSum =
    function
    | Summation(Power(r,k), var, start, n)
        when start = 0Q && k = var ->
        if n = infinity then 1/(1-r)
        else (1-r**(n+1))/(1-r)
    | Summation(Product [Power(r,k); a], var, start, n)
    | Summation(Product [a; Power(r,k)], var, start, n)
        when start = 0Q && k = var ->
        if n = infinity then a * (1/(1-r))
        else a * (1-r**(n+1))/(1-r)
    | x -> x


let quadraticSequenceNth n sequence =
    let sndDiff = sequence |> pairwiseDiff |> pairwiseDiff
    let u1, u2 = Seq.head sequence, Seq.head (Seq.tail sequence)
    maybe {
        let! _ = Expression.toFloat u1
        match (set (Seq.map Expression.forceToFloat sndDiff)).Count with
        | 1 ->
            let d = Seq.head sndDiff
            let a = d/2Q
            let b = -3*a + (u2 - u1)
            let c = -(a + b) + u1
            return a * n**2Q + b * n + c
        | _ -> return! None
    }

/// condition: n >= 0
let binomialTheorem = 
    printfn "n >= 0"
    function
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

let rewriteAsExpectation = function
    | FunctionN(SumOver,x::_) as f ->
        maybe {
            let! p = Structure.first Prob.isProb x
            let! x' = Structure.recursiveFilter ((<>) p) x
            return (expectation p x')
        } |> Option.defaultValue f
    | f -> f

let rewriteExpectationAsSum = function
    | IsExpectation(expr, distr) ->
        match Structure.first Expression.isVariable (Prob.inner distr) with
        | Some dx -> FunctionN(SumOver, [(distr * expr);dx])
        | None -> FunctionN(SumOver, [(distr * expr)])
    | f -> f

let expandVarianceExpectation = function
    | IsExpectation
        (Power (Sum [Product [Number n; IsExpectation(x1, p1)]; x2], p),p2) when n = -1N && p = 2Q ->
            expectation p1 (x1**2Q) - (expectation p2 x2)**2Q
    | x -> x