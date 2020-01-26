﻿module MathNet.Symbolics.Summation

open MathNet.Numerics
open MathNet.Symbolics
open MathNet.Symbolics.NumberTheory
open MathNet.Symbolics.Core
open Utils
open Operators 
open Prelude.Common

let summation var start stop fx = FunctionN(SumOver, [fx;var;start;V"="; stop])

let (|Summation|_|) input =
     match input with
     | FunctionN(SumOver, [fx;var;start;_; stop]) -> Some(fx,var,start, stop)
     | _ -> None

let isSummation = function | Summation _ -> true | _ -> false

let extractSumConstants = function
    | Summation(p,v,start,stop) ->
         Expression.extractNonVariables v (summation v start stop) p
    | x -> x

let expandSummation = function
    | Summation(Sum _ as s,v,start,stop) ->
         Expression.expandSumsOrProducts (summation v start stop) s
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

/// condition: r <= 1, r > 0
let simplifyInfiniteGeometricSum = function
    | Summation(Power(r,k), var, start, n)
        when start = 0Q && k = var && n = infinity -> 1/(1-r)
    | Summation(Product [Power(r,k); a], var, start, n)
    | Summation(Product [a; Power(r,k)], var, start, n)
        when start = 0Q && k = var && n = infinity ->
        a * (1/(1-r))
    | x -> x

/// condition: n >= 0
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

let rewriteAsExpectation = function
    | FunctionN(SumOver,x::_) as f ->
        maybe {
            let! p = Structure.first isProb x
            let! x' = Structure.recursiveFilter ((<>) p) x
            return (expectation p x')
        } |> Option.defaultValue f
    | f -> f

let rewriteExpectationAsSum = function
    | IsExpectation(expr, distr) ->
        let dx =
            match Structure.first Expression.isVariable (innerProb distr) with
            | Some e -> e  
            | None -> V""
        FunctionN(SumOver, [(distr * expr);dx;V"";V"";V""])
    | f -> f

let expandVarianceExpectation = function
    | IsExpectation 
        (Power (Sum [Product [Number n; IsExpectation(x1, p1)]; x2], p),p2) when n = -1N && p = 2Q -> 
            expectation p1 (x1**2Q) - (expectation p2 x2)**2Q
    | x -> x