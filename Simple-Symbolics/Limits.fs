module MathNet.Symbolics.Limits

open MathNet.Symbolics.Core
open Utils
open NumberProperties.Expression
open Operators
open NumberProperties

 
let extractConstants = function
    | IsLimit(var,lim,x) ->
        Structure.extractConstantAndApplyF (limit var lim) x
    | x -> x

let extractNonVariables = function
    | IsLimit(var,lim,x) ->
        Structure.extractNonVariablesAndApplyF var (limit var lim) x
    | x -> x

let sumRule = function
    | FunctionN(Limit,[var;lim;Sum l]) ->
        Sum (List.map (limit var lim) l)
    | x -> x

let productRule = function
    | FunctionN(Limit,[var;lim;Product l]) ->
        Product (List.map (limit var lim) l)
    | x -> x

let divisionRule = function
    | IsLimit(var,lim,r) ->
        (limit var lim (Rational.numerator r))/ (limit var lim (Rational.denominator r))
    | x -> x

let powerRule = function
    | FunctionN(Limit,[var;lim;Power(x,n)]) when isNumber n ->
        (limit var lim x)**n
    | x -> x

let constantRule = function
    | FunctionN(Limit,[var;lim;IsNumber n]) -> n
    | x -> x

///when limit variable and limit are the same
let varRule = function
    | FunctionN(Limit,[var;lim;x]) when x = var -> lim
    | x -> x

let evaluate = function
    | FunctionN(Limit,[var;lim;x]) ->
        hold(replaceSymbolWith lim var x)
    | x -> x

let atInfinity = function
    | FunctionN(Limit,[var;lim;x]) as v ->
        let n = Rational.numerator x
        let d = Rational.denominator x
        match (n,d) with
        | IsNumber _, Power(Identifier _ as i, (Number _ as b)) when i = var ->
            if isInfinity lim && Expression.isPositive b = Some true then 0Q
            else v
        | IsNumber _, (Identifier _ as i) when i = var ->
            if isInfinity lim then 0Q else v
        | _ -> v
    | v -> v

let applyFn f = function
    | IsLimit(v,l,x) -> limit v l (f x)
    | x -> x

module Polynomials =
    let divisionTrick x px =
        printfn "%A %A" x px
        if Polynomial.isPolynomial x px then
            let deg = Polynomial.degree x px
            Product[x**deg ; px / (x**deg) |>  Algebraic.expand]
        else px

    let extractMaxTerm x px =
        if Polynomial.isPolynomial x px then
            let coeffs = Polynomial.coefficients x px
            coeffs.[^0] * x ** (coeffs.Length - 1)
        else px

let bringAbsOutsideLimit = function
    |IsLimit(v, l, Function(Abs,x)) -> abs (limit v l x)
    | x -> x

let ratioTest n x =
    let innerx = replaceSymbolWith (n+1) n x
    limit n infinity (abs (innerx/x))