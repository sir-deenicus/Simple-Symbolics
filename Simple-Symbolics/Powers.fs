﻿namespace MathNet.Symbolics
open Core

module Logarithm =

    let expand =
        function
        | Function(Ln, Product l) ->
            Sum(List.map (function
                    | Power(x, n) when n = -1Q -> -ln x
                    | x -> ln x) l)
        | f -> f

    let contract =
        function
        | Sum l as f ->
            let logs, rest =
                List.partition (function
                    | Function(Ln, _) -> true
                    | Product [ n; Function(Ln, _) ] when n = -1Q -> true
                    | _ -> false) l

            let logs' =
                logs
                |> List.map (function
                       | Product [ n; Function(Ln, x) ] when n = -1Q -> 1 / x
                       | Function(Ln, x) -> x
                       | _ -> failwith "never")

            match logs' with
            | [] -> f
            | _ -> ln (Product logs') + Sum rest
        | f -> f

    let internal powerRuleSingle =
        function
        | Function(Ln, Power(x, n)) -> n * Function(Ln, x)
        | FunctionN(Log, [b; Power(x, n)]) -> n * FunctionN(Log, [b;x])
        | f -> f

    let rec powerRule =
        function
        | Product l -> Product(List.map powerRule l)
        | Sum l -> Sum(List.map powerRule l)
        | f -> powerRuleSingle f

    let internal powerRuleSingleBackwards =
        function
        | Product[a; Function(Ln, x)] -> Function(Ln, (x**a))
        | Product[a; FunctionN(Log, [b;x])] -> FunctionN(Log,[b; (x**a)])
        | f -> f

    let rec powerRuleBackwards =
        function
        | Product l -> Product(List.map powerRuleSingleBackwards l)
        | Sum l -> Sum(List.map powerRuleSingleBackwards l)
        | f -> powerRuleSingleBackwards f

module Exponents =
    let movePowerLeft nInt =
        let n = Expression.FromInt32 nInt
        function
        | Power(b, (Sum(Number _ :: _) as r)) ->
            Core.Algebraic.simplifyLite (b ** n * Power(b, r - n))
        | f -> f

    let splitPower =
        function
        | Function(Exp, Sum l) ->
            Core.Algebraic.simplifyLite (List.map exp l |> Product)
        | Power(b, (Sum l)) ->
            Core.Algebraic.simplifyLite (List.map (fun e -> b ** e) l |> Product)
        | f -> f

    let replaceExpWithE = function
    | Function(Exp, x) -> 
        Power(Constant (Constant.E),x)
    | f -> f

    let replaceEWithExp = function
        | Power(Constant (Constant.E),x) -> 
            Function(Exp, x)
        | f -> f