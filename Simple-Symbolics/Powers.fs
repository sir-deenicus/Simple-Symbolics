namespace MathNet.Symbolics
open Core
open Utils 
open NumberProperties 
open MathNet.Numerics

module Logarithm =
    open MathNet.Symbolics.Operators 
    open NumberProperties 
    
    let changeOfBaseRule targetBase =
        function
        | FunctionN(Log, [ b; x ]) ->
            match targetBase with
            | Constant Constant.E -> ln x / ln b
            | _ -> log targetBase x / log targetBase b
        | Function(Ln as f, x) | Function(Log as f, x) ->
            let b =
                match f with
                | Ln -> Constants.e
                | Log -> 10Q
                | _ -> failwith "unreachable"
            match targetBase with
            | Constant Constant.E -> ln x / ln b
            | _ -> log targetBase x / log targetBase b
        | x -> x


    ///log (a * b) -> log a + log b
    let expand =
        function
        | Function (Ln,Power (x,n)) when n = -1Q -> -ln x
        | FunctionN (Log,[b; Power (x,n)]) when n = -1Q ->
            log b 1Q - log b x
        | Function (Ln, NonIntegerRational (a,b)) -> ln (ofBigInteger a) - ln (ofBigInteger b)
        | FunctionN(Log, [b; NonIntegerRational (n,m)]) -> log b (ofBigInteger n) - log b (ofBigInteger m)
        | Function(Ln, Products(fx,var,start, stop)) -> summation var start stop (ln fx)
        | Function(Ln, Product l) ->
            Sum(List.map (function
                    | Power(x, n) when n = -1Q -> -ln x
                    | x -> ln x) l)
        | FunctionN(Log, [b;Product l]) ->
            Sum(List.map (function
                    | Power(x, n) when n = -1Q -> -log b x
                    | x -> log b x) l)
        | f -> f

    ///log a + log b + ... -> log (a*b...)
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
                       | _ -> failwith ("should \"never\" occur error encountered in Logarithm.contract with " + (Infix.format f)))

            match logs' with
            | [] -> f
            | _ -> ln (Product logs') + Sum rest
        | f -> f

    let private powerRuleSingle =
        function
        | Function(Ln, Power(x, n)) -> n * Function(Ln, x)
        | FunctionN(Log, [b; Power(x, n)]) -> n * FunctionN(Log, [b;x])
        | f -> f

    ///log (x**n) -> n * log x
    let rec powerRule =
        function
        | Product l -> Product(List.map powerRule l)
        | Sum l -> Sum(List.map powerRule l)
        | f -> powerRuleSingle f

    ///a * log x -> log(x^a)
    let powerRuleReverse vx =
        match vx with
        | Product[a; Function(Ln, x)] -> Function(Ln, (x**a))
        | Product[a; FunctionN(Log, [b;x])] -> FunctionN(Log,[b; (x**a)])
        | Product ps as f ->
            let haslog, rest = List.partition Expression.containsLog ps
            match haslog with 
            | [FunctionN(Log, [b;x])] -> FunctionN(Log, [b; (x** Product rest)] )
            | [Function(Ln, x)] -> Function(Ln, (x** Product rest) )
            | _ -> f 
        | f -> f 

    let Simplify = function
        | Function(Ln, Power(Constant Constant.E, x))
        | Function(Ln, Function(Exp, x)) -> x
        | FunctionN(Log, [_;n]) when n = 1Q -> 0Q
        | FunctionN(Log, [a;Power(b,x)]) when a = b ->  x 
        | FunctionN(Log, [a;b]) when a = b -> 1Q
        | FunctionN(Log, [Approximation (Real b); Number a]) 
        | FunctionN(Log, [Number a;Approximation (Real b)]) as z ->  
            if a = BigRational.fromFloat64 b then 1Q 
            else z  
        | Power(Constant Constant.E, Function(Ln,x))
        | Function(Exp, Function(Ln, x)) -> x
        | x -> x 
    
    let eval = function 
        | Function(Ln, Number n) -> Number (BigRational.log n)
        | FunctionN(Log, [Number b; Number n]) -> Number (BigRational.log n / BigRational.log b)
        | x -> x    

module Exponents =
    let shiftPowerLeftRaw (n:Expression) =
        function
        | Power(b, r) ->
             (b ** n * hold(Power(b, hold r - n)))
        | f -> f

    let shiftPowerLeft (n:Expression) =
        function
        | Power(b, r) ->
             (b ** n * hold(Power(b, r - n)))
        | f -> f
         
    let splitPower =
        function
        | Function(Exp, Sum l) ->
            Core.Expression.simplifyLite (List.map (exp >> hold) l |> Product)
        | Power(b, (Sum l)) ->
            Core.Expression.simplifyLite (List.map (fun e -> hold(b ** e)) l |> Product)
        | f -> f

    let replaceExpToE = function
        | Function(Exp, x) -> 
            Power(Constant (Constant.E),x)
        | f -> f

    let replaceEtoExp = function
        | Power(Constant (Constant.E),x) -> 
            Function(Exp, x)
        | f -> f 

    let powerRule = function
        | Power(Power(x, a), b) -> Power(x, (a * b))
        | Power(Product l, b) ->   
            let rec loop acc = function
                | [] -> Product acc
                | (Power(x, a))::xs -> loop (Power(x, (a * b))::acc) xs
                | x::xs -> loop (x**b::acc) xs
            loop [] l 
        | x -> x 

    let powerRuleRev dohold = function
        | Power(a,Product[Number _ as n;x;y]) ->
            let res = a**(n*x)
            if dohold then (hold res)**y else res**y
        | Power(a,Product[x;y]) ->
            let res = a**x
            if dohold then (hold res)**y else res**y
        | x -> x

    let powerRuleRevAlt dohold = function
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
    ///This process is essentially the reverse of applying the **Power of a Product Rule** (which states that `(a * b)^n = a^n * b^n`).
    let gatherProductPowers x = 
        match Expression.simplifyLite x with //collapse any nested products
        | Product ls -> //only for products
            //As before, split by qualifed
            let qualify, rest =
                ls
                |> List.partition (function
                    | Id (Power _, _)
                    | Power _ -> true
                    | _ -> false)

            //Of those that qualify, this time group by their exponents. Ignoring signs.
            let grouped =
                qualify
                |> List.groupBy (function
                    | Id (Power (_,x), _)
                    | Power(_,x) -> abs(x) |> Expression.cancelAbs
                    | y -> y)

            //divide the powers through by the common exponent as we're taking it outside of the product 
            let groupedProduct =
                [ for (exponent, exprs) in grouped do
                    let v =
                        exprs
                        |> List.map (function
                            | Power(x, p) -> x ** (p / exponent)
                            | Id(Power(x, p), strtag) -> Id(x ** (p / exponent), strtag)
                            | _ -> Operators.undefined) //unreachable by partition def
                        |> Product
                    yield v ** exponent] 
            match rest with 
            | [] -> Product groupedProduct 
            | _ -> Product (groupedProduct @ rest)
        | x -> x

//carry around enforced equalities, eg b > 0
module SquareRoot =
    let splitDivisionInRadical = function
        | Power(Number x, Number n) when n = (1N/2N) && x.Denominator <> 0I -> sqrt (ofBigInteger x.Numerator) / sqrt (ofBigInteger x.Denominator)
        | Power(Divide(a,b), Number n) when n = (1N/2N) && b <> 0Q -> sqrt a / sqrt b
        | Power(Number x, Number n) when n = (-1N/2N) && x.Denominator <> 0I -> sqrt (ofBigInteger x.Denominator) / sqrt (ofBigInteger x.Numerator) 
        | Power(Divide(a,b), Number n) when n = (-1N/2N) && b <> 0Q -> sqrt b/sqrt a
        | x -> x
    let bringPowerOutsideRadical = function
        | Power(Power(a,n), Number m) when m = (1N/2N) -> (sqrt a)**n
        | x -> x 