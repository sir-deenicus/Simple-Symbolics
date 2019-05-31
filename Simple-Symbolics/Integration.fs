module MathNet.Symbolics.Integration

open MathNet.Symbolics
open System.Numerics
open MathNet.Numerics
open MathNet
open Operators
open Core
open Core.Vars

module Option =
    let mapOrAdd def f =
        function
        | None -> Some def
        | Some y -> Some(f y)

let integral dx x = FunctionN(Integral, [ x; dx ])

let integratePolynomExpr m n e = e ** (n + 1Q) / (m * (n + 1Q))

let isLinear x f =
    Polynomial.isPolynomial x f && (Polynomial.degree x f).ToFloat() = 1.

let intFuncStraight =
    function
    | Function(Cos, (x)) -> Function(Sin, x)
    | Function(Sin, x) -> -Function(Cos, x)
    | Function(Tan, x) -> -ln (cos x)
    | Function(Ln, x) -> x * Function(Ln, x) - x
    | Function(Log, x) -> x * Function(Log, x) - x
    | Function(Exp, x) -> Function(Exp, x)
    | _ -> failwith "function unmet"

let extractLinearComponent x ex =
    let e' = Polynomial.collectTerms x ex
    let l = Algebraic.summands e'
    let matches, _ = List.partition (containsVar x) l
    match matches with
    | [ Identifier(Symbol _) as x' ] when x = x' -> 1Q, e'
    | [ Product l ] ->
        match List.filter ((<>) x) l with
        | [ t ] -> t, e'
        | _ -> failwith "Could not extract terms in power"
    | _ -> failwith "Power attempt failed, not a product"

let linearSquared combinator =
    combinator (function
        | Power(e, n) when n = 2Q && isLinear x e -> true
        | _ -> false)

type IntegrationResult =
    | Succeeded of Expression
    | Partial of Success : Expression * Defer : Expression * IsSum : bool
    | Deferred of Expression * bool

let justSuccess =
    function
    | Succeeded e -> e
    | _ -> failwith "could not extract"

let integrateSimplePartial x f =
    let rec iter =
        function
        | Number _ as n -> Succeeded(n * x)
        | Identifier(Symbol _) as vx ->
            if vx = x then Succeeded(vx ** 2 / 2)
            else Succeeded(vx * x)
        | f when f = 1 / (1 + x ** 2) -> Succeeded(arctan x)
        | Power(Sum l, neg1) as f when neg1 = -1Q && linearSquared List.exists l ->
            let ex, l' = linearSquared List.partition l
            let n = Sum l'
            match ex with
            | [ Power(e, _) ] ->
                let m, _ = extractLinearComponent x e
                let fx =
                    arctan (e / (sqrt n)) / (m * sqrt n)
                    |> Algebraic.simplify true
                Succeeded fx
            | _ -> Deferred (f, false)
        | f when f = 1 / (sqrt (1 - x ** 2)) -> Succeeded(arcsin x)
        | Power(e, n) as p when not (containsVar x e) && not (containsVar x n) ->
            Succeeded(p * x)
        | Power(e, n) as p when not (containsVar x e) && (containsVar x n)
                                && isLinear x n ->
            Succeeded(p / (fst (extractLinearComponent x n) * ln (e)))
        | Power(e, n) as f when not (containsVar x e) && (containsVar x n) ->
            //printfn "Power nonlinear in x, fail"
            Deferred (f,false)
        | Power(e, n) when n = -1Q && e <> 0Q && isLinear x e ->
            Succeeded(Function(Ln, e) / fst (extractLinearComponent x e))
        | Power(Identifier _ as y, n) when x = y && n <> -1Q ->
            Succeeded((x ** (n + 1)) / (n + 1))
        | poly when Polynomial.isMonomial x poly ->
            let k, mono = Algebraic.separateFactors x poly
            match (iter mono) with
            | Succeeded fx -> Succeeded(k * fx)
            | _ -> failwith "unexpected state in integrate monomial"
        | Power(Sum _ as e, n) when isLinear x e && n <> -1Q ->
            let t, e' = extractLinearComponent x e
            Succeeded(integratePolynomExpr t n e')
        | Power(e, n) as poly when Polynomial.isPolynomial x e && n <> -1Q ->
            Succeeded(poly
                     |> Algebraic.expand
                     |> Algebraic.summands
                     |> List.map (iter >> justSuccess)
                     |> Sum)
        | Function(f, (Identifier(Symbol _) as y)) when x <> y ->
            Succeeded(x * Function(f, y))
        | Function(f, (Number _ as n)) -> Succeeded(x * Function(f, n))
        | Function(_, (Identifier(Symbol _))) as f ->
            Succeeded(intFuncStraight f)
        | Function(_, ex) as f when isLinear x ex ->
            Succeeded((intFuncStraight f) / fst (extractLinearComponent x ex))
        | Sum l ->
            let calculated, deferred =
                List.fold (fun (sums, fails) r ->
                    match r with
                    | Succeeded g -> sums |> Option.mapOrAdd g ((+) g), fails
                    | Partial (Success = g; Defer = f) ->
                        sums, (g * integral x f)::fails
                    | Deferred (f,_) -> sums, (integral x f)::fails)
                    (None, []) (List.map iter l) 
            match calculated, deferred with
            | Some f, [] -> Succeeded f 
            | Some f, l -> Partial(f, List.sum l, true)
            | None, [] ->
                failwith
                    (sprintf "Unexpected error integrating %s"
                         (Expression.toFormattedString (Sum l))) 
            | None, f -> Deferred (List.sum f, true)         

        | Product _ as e ->
            let k, e' = Algebraic.separateFactors x e
            if k = 1Q then
                //printfn "Separating factors, no x found."
                Deferred (e,false)
            else
                match (iter e') with
                | Succeeded good -> Succeeded(k * good)
                | Partial(good, fail, t) -> Partial((k * good), fail, t)
                | Deferred (fail,t) -> Partial(k, fail, t)
        | f when not (containsVar x f) -> Succeeded(x * f)
        | f -> Deferred (f,false)
            (*printfn "Can't integrate this %s" (f.ToFormattedString());*) 
    iter f

let rec integrateSimple x =
    function
    | Number _ as n -> n * x
    | Identifier(Symbol _) as vx ->
        if vx = x then vx ** 2 / 2
        else vx * x
    | f when f = 1 / (1 + x ** 2) -> arctan x
    | Power(Sum l, neg1) when neg1 = -1Q && linearSquared List.exists l ->
        let ex, l' = linearSquared List.partition l
        let n = Sum l'
        match ex with
        | [ Power(e, _) ] ->
            let m, _ = extractLinearComponent x e
            arctan (e / (sqrt n)) / (m * sqrt n) |> Algebraic.simplify true
        | _ -> failwith "err"
    | f when f = 1 / (sqrt (1 - x ** 2)) -> arcsin x
    | Power(e, n) as p when not (containsVar x e) && not (containsVar x n) ->
        p * x
    | Power(e, n) as p when not (containsVar x e) && (containsVar x n)
                            && isLinear x n ->
        p / (fst (extractLinearComponent x n) * ln (e))
    | Power(e, n) when not (containsVar x e) && (containsVar x n) ->
        failwith "Power nolinear in x, fail"
    | Power(e, n) when n = -1Q && e <> 0Q && isLinear x e ->
        Function(Ln, e) / fst (extractLinearComponent x e)
    | Power(Identifier _ as y, n) when x = y && n <> -1Q ->
        (x ** (n + 1)) / (n + 1)
    | poly when Polynomial.isMonomial x poly ->
        let k, mono = Algebraic.separateFactors x poly
        k * integrateSimple x mono
    | Power(Sum _ as e, n) when isLinear x e && n <> -1Q ->
        let t, e' = extractLinearComponent x e
        integratePolynomExpr t n e'
    | Power(e, n) as poly when Polynomial.isPolynomial x e && n <> -1Q ->
        poly
        |> Algebraic.expand
        |> Algebraic.summands
        |> List.map (integrateSimple x)
        |> Sum
    | Function(f, (Identifier(Symbol _) as y)) when x <> y -> x * Function(f, y)
    | Function(f, (Number _ as n)) -> x * Function(f, n)
    | Function(_, (Identifier(Symbol _))) as f -> intFuncStraight f
    | Function(_, ex) as f when isLinear x ex ->
        (intFuncStraight f) / fst (extractLinearComponent x ex)
    | Sum l -> Sum(List.map (integrateSimple x) l)
    | Product _ as e ->
        let k, e' = Algebraic.separateFactors x e
        if k = 1Q then failwith "Separating factors, no x found. Aborting."
        else k * integrateSimple x e'
    | f when not (containsVar x f) -> x * f
    | x -> failwith "Can't integrate this"
     
let usubst outer diffx =
    function
    | Power(x, _) | Function(_, x) -> outer / Calculus.differentiate diffx x
    | _ -> failwith "unimplemented compute size"

let integratePartialRes x e =
    match (integrateSimplePartial x e) with 
    | Partial(s, def, true) -> s + def, false
    | Partial(s, def, false) -> s * (integral x def), false
    | Succeeded e -> e, true
    | Deferred (e,true) -> e, false
    | Deferred (e,false) -> integral x e, false

let integratePartial x e = fst(integratePartialRes x e)

let (|IsIntegral|_|) = function
     | FunctionN(Integral, [ x; dx ]) -> Some(x,dx)
     | _ -> None

let evalIntegral =
    function
    | IsIntegral(f, dx) -> integratePartial dx f
    | f -> f

let rewriteIntegralAsExpectation = function
    | FunctionN(Function.Integral, Product l :: _) as f ->
        maybe {
            let! p = List.tryFind (function
                         | FunctionN(Probability, _) -> true
                         | _ -> false) l
            return FunctionN(Function.Expectation,
                             [ (Product l) / p; p ]) } |> Option.defaultValue f
    | f -> f  

module Riemann =
    let toSum x b a f =
        let dx = (b - a) / n
        let x_i = a + dx * i
        dx * replaceExpression x_i x f

    let displaylimit x =
        x
        |> Expression.toFormattedString
        |> sprintf @"\lim _{n \rightarrow \infty} \sum_{i=1}^{n}%s"
