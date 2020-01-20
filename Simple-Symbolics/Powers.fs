namespace MathNet.Symbolics
open Core
open Utils 

module Logarithm =
    open MathNet.Symbolics.Operators

    let expand =
        function
        | Function(Ln, Product l) ->
            Sum(List.map (function
                    | Power(x, n) when n = -1Q -> -ln x
                    | x -> ln x) l)
        | FunctionN(Log, [b;Product l]) ->
            Sum(List.map (function
                    | Power(x, n) when n = -1Q -> -log b x
                    | x -> log b x) l)
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
            Core.Expression.simplifyLite (b ** n * Power(b, r - n))
        | f -> f

    let splitPower =
        function
        | Function(Exp, Sum l) ->
            Core.Expression.simplifyLite (List.map (exp >> hold) l |> Product)
        | Power(b, (Sum l)) ->
            Core.Expression.simplifyLite (List.map (fun e -> hold(b ** e)) l |> Product)
        | f -> f

    let replaceExpWithE = function
        | Function(Exp, x) -> 
            Power(Constant (Constant.E),x)
        | f -> f

    let replaceEWithExp = function
        | Power(Constant (Constant.E),x) -> 
            Function(Exp, x)
        | f -> f

    let powerRule = function
        | Power(Power(x, a), b) -> Power(x, (a * b))
        | x -> x 

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

    // To apply the product rule of exponents, first I want to take a product and extract all which qualify.
    let productRule =
        function
        | Product ls ->
            let qualify, rest =
                ls
                |> List.partition (function
                    | Identifier _
                    | Power _ -> true
                    | _ -> false)

            //Of those that qualify, group by their base.
            let grouped =
                qualify
                |> List.groupBy (function
                    | Identifier _ as x
                    | Power(x, _) -> x
                    | y -> y)

            //The task now is to sum by the exponents and raise to this new power
            let groupedPowers =
                grouped
                |> List.map (fun (x, xs) ->
                    let exponents = // sum exponrnyd
                        xs
                        |> List.sumBy (function
                            | Identifier _ -> 1Q
                            | Power(_, n) -> n
                            | _ -> 0Q) //unreachable by def of partition
                    x ** exponents)

            //Now combine with rest
            Product(rest @ groupedPowers)
        | x -> x

    let expandRationalPower = function
        | Power(a,b) as x ->
            let den = Rational.denominator a 
            if den = 1Q then x
            else
                let num = Rational.numerator a
                num**b/(den**b) 
        | x -> x

    //sometimes it's necessary to gather exponents back into parentheses.
    let gatherProductPowers x = 
        match Expression.simplifyLite x with //collapse any nested products
        | Product ls -> //only for products
            //As before, split by qualifed
            let qualify, rest =
                ls
                |> List.partition (function
                    | Id (Power _)
                    | Power _ -> true
                    | _ -> false)

            //Of those that qualify, this time group by their exponents. Ignoring signs.
            let grouped =
                qualify
                |> List.groupBy (function
                    | Id (Power (_,x))
                    | Power(_,x) -> abs(x) |> Expression.cancelAbs
                    | y -> y)

            //divide the powers through by the common exponent as we're taking it outside of the product 
            let groupedProduct =
                [ for (exponent, exprs) in grouped do
                    let v =
                        exprs
                        |> List.map (function
                            | Power(x, p) -> x ** (p / exponent)
                            | Id(Power(x, p)) -> Id(x ** (p / exponent))
                            | _ -> Operators.undefined) //unreachable by partition def
                        |> Product
                    yield v ** exponent] 
            match rest with 
            | [] -> Product groupedProduct 
            | _ -> Product (groupedProduct @ rest)
        | x -> x