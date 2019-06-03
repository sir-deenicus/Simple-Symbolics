#load "Core.fsx"

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

module Riemann =
    let toSum x b a f =
        let dx = (b - a) / n
        let x_i = a + dx * i
        dx * replaceExpression x_i x f

    let displaylimit x =
        x
        |> Expression.toFormattedString
        |> sprintf @"\lim _{n \rightarrow \infty} \sum_{i=1}^{n}%s"

let usubst outer diffx =
    function
    | Power(x, _) | Function(_, x) -> outer / Calculus.differentiate diffx x
    | _ -> failwith "unimplemented compute size"

let integratePartial x e =
    match (integrateSimplePartial x e) with 
    | Partial(s, def, true) -> s + def
    | Partial(s, def, false) -> s * (integral x def)
    | Succeeded e 
    | Deferred (e,true) -> e
    | Deferred (e,false) -> integral x e


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
// integrateSimple x (1 / ((a * x + x + b) ** 2 + 1)) |> Infix.format
// integrateSimple x (1 / (1 * (a * x + x + b) ** 2 + b)) |> Infix.format
// integrateSimple x (1 / (((a + 2) * x + b + c + x) ** 2 + c + y)) |> Infix.format //Caveats
// integrateSimple x (1 / ((a * x + b) ** 2 + 0)) |> Infix.format
// integrateSimple x (1 / ((1 + x))) |> Infix.format
// integrateSimple x (5Q ** (3 * x + 1)) |> Infix.format
// integrateSimple x (exp x) |> Infix.format
// integrateSimple x (exp (x + 1 + a * x)) |> Infix.format
// integrateSimple x (log (x + 1 + a * x)) |> Infix.format
// integrateSimple x ((a * x + b * x + 3) ** 2) |> Infix.format
// integrateSimple x ((x ** 2 * a * b) ** 2) |> Infix.format
// integrateSimple x (1 / sqrt x) |> Infix.format
// integrateSimple x (1 / sqrt (x + 1)) |> Infix.format
// integrateSimple x (cos (x + 1)) |> Infix.format
// integrateSimple x (1 / (3 * x + 1)) |> Infix.format
// integrateSimple x ((a * x + 3) ** 2) |> Infix.format
// integrateSimple x ((a * x ** 2 + 3) ** 2) |> Infix.format
// integrateSimple x ((a * x + b * x ** 2 + 3) ** 2) |> Infix.format
// integrateSimple x (1 / x) |> Infix.format
// ((x ** 2 * a + 3) ** 2)
// |> Algebraic.expand
// |> integrateSimple x
// |> Infix.format
// integrateSimple x (1 / (x + 1) ** a) |> Infix.format //Caveats
// integrateSimple t a
// |> integrateSimple t
// |> Infix.format
// integrateSimple t (a * t + v0) |> Infix.format
// csc (2 * x + 1) * cot (2 * x + 1) |> Trigonometric.separateFactors // |> Infix.format
///////////BROKE
//integrateSimple x (1/( sqrt(1 - 16 * x **2) )) |> Infix.format
//integrateSimple x (1/((3 * (a * x)**2 + 1))) |> Infix.format
//integrateSimple x (1/((a * x)**2 + 1) ) |> Infix.format
//integrateSimple x (a * x * cos x) |> Infix.format
//integrateSimple x (1/(3*x**2+1)) |> Infix.format
//integrateSimple x (1/cos(x))|> Infix.format
//integrateSimplePartial x (5 * x + 1/cos(x))

// (integratePartial x (a * exp(x**2) + b * exp(x**2))) |> writeExpr

// integratePartial x (prob x * x**2 + prob x * 2 * x) |> Structure.recursiveMap rewriteIntegralAsExpectation|> writeExpr

// integratePartial x (prob x * x**2 + prob x * 2 * x)  |> writeExpr 
// integrateSimple x (sin (x) ** 2 |> Trigonometric.simplify) |> writeExpr

// let ex, tr = integral x (cos (sqrt x)/(sqrt x)) |> usubstitutionSteps  
// let ex, tr = integral x (exp (2*x) / (8 + exp (2*x))) |> usubstitutionSteps
// let ex, tr = integral y ((3 * exp (3*sqrt y)) / (sqrt y)) |>evalIntegral |> usubstitutionSteps
// integral y ((3 * exp (3*sqrt y)) / (sqrt y)) |> evalIntegral |> writeExpr
// string tr |> writeStr
// writeExpr ex
// integral x (Product [sin(x ** 4);x **3]) |> usubstitution  |> writeExpr
// integral x (sin(7*x ** 4 + 3) * x **3) |> usubstitution |> writeExpr
    
// usubstitution (integral x (x * cos(x**2))) |> writeExpr 
// usubstitutionSteps (integral x (x * 2 * cos(x))) |> snd |> string |> writeStr
  