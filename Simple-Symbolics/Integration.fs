module MathNet.Symbolics.Integration

open MathNet.Symbolics
open System.Numerics
open MathNet.Numerics
open MathNet
open Operators
open Core
open Core.Vars
open Utils
open MathNet.Symbolics.Differentiation
open Prelude.Common

let (|IsIntegral|_|) = function
     | FunctionN(Integral, [ x; dx ]) -> Some(x,dx)
     | _ -> None

let (|IsDefiniteIntegral|_|) = function
     | FunctionN(Integral, [ x; dx;a;b ]) -> Some(x,dx,a,b)
     | _ -> None
 
let integral dx x = FunctionN(Integral, [ x; dx ])

let defintegral dx a b x = FunctionN(Integral, [ x; dx; a; b ])

let rewriteIntegralAsSum = function 
   | IsIntegral(x,(Identifier (Symbol sdx) as dx)) -> PSigma.sum(Product[x;V("\Delta " + sdx)],dx,V"",V"",Expression.PositiveInfinity)     
   | x -> x
 
module Expression =
    let isIntegral = function IsIntegral _ -> true | _ -> false

module Integral =
    let inner = function IsIntegral(f,_) | IsDefiniteIntegral(f,_,_,_) -> f | f -> f
    let integratingVar = function 
        | IsIntegral(_,dx) 
        | IsDefiniteIntegral(_,dx,_,_) -> Some dx 
        | _ -> None
    let toDefinite a b = function
        | IsIntegral (f, dx) ->  defintegral dx a b f
        | f -> f

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

let extractLinearComponentTest x ex =
    let e' = Polynomial.collectTerms x ex
    let l = Algebraic.summands e'
    let matches, _ = List.partition (containsVar x) l
    match matches with
    | [ Identifier(Symbol _) as x' ] when x = x' -> Ok (1Q, e')
    | [ Product l ] ->
        match List.filter ((<>) x) l with
        | [ t ] -> Ok(t, e')
        | [Number n; z] when n = -1N -> Ok(-z, e')
        | _ -> Error "Could not extract terms in power"
    | _ -> Error "Power attempt failed, not a product"

let extractLinearComponent x ex = 
    match (extractLinearComponentTest x ex) with
    | Ok r -> r 
    | Error e -> failwith e

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
        | Approximation _ as r -> Succeeded (r * x)
        | Identifier(Symbol _) as vx ->
            if vx = x then Succeeded(vx ** 2 / 2)
            else Succeeded(vx * x)
        | f when f = 1 / (1 + x ** 2) -> Succeeded(arctan x)
        | Power(Sum l, neg1) as f when neg1 = -1Q && linearSquared List.exists l ->
            let ex, l' = linearSquared List.partition l
            let n = Sum l'
            match ex with
            | [ Power(e, _) ] ->
                match extractLinearComponentTest x e with
                | Ok (m,_) -> 
                    let fx =
                        arctan (e / (sqrt n)) / (m * sqrt n)
                        |> Algebraic.simplify true
                    Succeeded fx
                | _ -> Deferred (f, false)
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
            Succeeded(Function(Ln, abs e) / fst (extractLinearComponent x e))
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
      
let integratePartialRes x e =
    match (integrateSimplePartial x e) with 
    | Partial(s, def, true) -> s + def, false
    | Partial(s, def, false) -> s * (integral x def), false
    | Succeeded e -> e, true
    | Deferred (e,true) -> e, false
    | Deferred (e,false) -> integral x e, false

let integratePartial x e = fst(integratePartialRes x e)
 
let evalIntegral =
    function
    | IsIntegral(f, dx) -> integratePartial dx f
    | f -> f 

let evalDefiniteIntegral =
    function
    | IsDefiniteIntegral(f, dx,a,b) as fn -> 
        match integratePartialRes dx f with
        | (_, false) -> fn
        | (e, true) -> replaceSymbol b dx e - replaceSymbol a dx e
    | f -> f 
 
let evalDefiniteIntegralUsing integrator = function
    | IsDefiniteIntegral(f, dx,a,b) as fn ->
        match integrator f with
            | IsIntegral _ -> fn
            | e -> replaceSymbol b dx e - replaceSymbol a dx e
    | f -> f
 
let evalAsDefiniteIntegralAt dx a b e = 
    replaceSymbol b dx e - replaceSymbol a dx e
    
let rec integrateByParts2 order expr = 
    let doIntegrateByParts dx a b =
        let u = a 
        let du = D dx u 
        let dv = b 
        let v = evalIntegral (integral dx dv) 
        u * v - evalIntegral (integral dx (v * du))
    match expr with
    | IsIntegral(Product [a;b],dx) -> 
        if order = 1 then doIntegrateByParts dx a b else doIntegrateByParts dx b a
    | IsIntegral(f,dx) -> integrateByParts2 order (integral dx (Product [1Q; f]))
    | f -> f 

let rec integrateByParts expr = 
    let doIntegrateByParts prev dx a b =
        let u = a 
        let du = D dx u 
        let dv = b 
        let v = evalIntegral (integral dx dv) 
        let res = u * v - evalIntegral (integral dx (v * du)) 
        if Structure.existsRecursive (Expression.isIntegral) res then
           match prev with 
           | None -> res, false
           | Some ex -> if width ex > width res then res, false else ex,false
        else res, true
    match expr with
    | IsIntegral(Product [a;b],dx) -> 
        let res, ok = doIntegrateByParts None dx a b
        if ok then res
        else doIntegrateByParts (Some res) dx b a |> fst
    | IsIntegral(f,dx) -> integrateByParts (integral dx (Product [1Q; f]))
    | f -> f  

let substitution substarget expr = 
    let usub = symbol "u_{sub}"
    let inner dx innerExpr =
        let du = D dx substarget
        let innerExprTemp = replaceExpression usub substarget innerExpr
        if innerExprTemp <> innerExpr then
            let _, solvefor = Solving.reArrangeExprEquationX true dx (substarget,usub) 
            let innerExpr' = replaceExpression solvefor dx innerExprTemp 
            if innerExpr' <> innerExprTemp then 
                match integratePartialRes usub (du * innerExpr') with
                | res, true -> replaceSymbol substarget usub res
                | _, false -> expr  
            else expr
        else expr
    match expr with
    | IsIntegral(IsIntegral _, _) -> expr
    | IsIntegral(f,_) when substarget = f -> expr
    | IsIntegral(f, dx) -> inner dx f 
    | f -> f

let substitutionSteps substarget expr = 
    let usub = symbol "u_{sub}"
    let trace = StepTrace(sprintf "$%s$" (Expression.toFormattedString expr))
    let inner dx innerExpr =
        let du = D dx substarget
        let innerExprTemp = replaceExpression usub substarget innerExpr  
        if innerExprTemp <> innerExpr then
            let _, solvefor = Solving.reArrangeExprEquation dx (substarget,usub) 
            let innerExpr' = replaceExpression solvefor dx innerExprTemp 
            if innerExpr' <> innerExprTemp then 
                trace.Add (dx <=> solvefor)
                trace.Add
                    ("${0}$. Therefore ${1}$, so $d{2} = {3}d{4}$",
                    [|  usub <=> substarget |> string;
                        diff dx usub <=> du |> string;
                        fmt (usub) ;
                        fmt du
                        fmt dx|])    
                let integrand = (du * innerExpr')
                trace.Add(integral usub innerExpr' <=> integral usub integrand)
                match integratePartialRes usub integrand with
                | res, true ->  
                    trace.Add res
                    replaceSymbol substarget usub res, trace
                | _, false -> trace.Add("failed"); expr, trace   
            else trace.Add("Substitution not possible"); expr, trace 
        else trace.Add("Substitution not possible"); expr, trace
    match expr with
    | IsIntegral(IsIntegral _, _) -> trace.Add("Nested, skipping"); expr, trace
    | IsIntegral(f,_) when substarget = f -> 
        trace.Add ("not a valid substitution")
        expr, trace
    | IsIntegral(f, dx) -> inner dx f 
    | f -> f, trace
  
let uSubstitution expr =
    let usub = symbol "u_{sub}"

    let substitute n y (f : FuncType) =
        let f' = f.WrapExpression usub
        match integratePartialRes usub f' with
        | res, true -> n * replaceSymbol y usub res
        | f, false -> f 
    let inner dx innerExpr =
        match innerExpr with
        | Product [ AsFunction(f1, y1) as x1; AsFunction(f2, y2) as x2 ] ->
            match x2 / (D dx y1) with
            | Number _ as n -> substitute n y1 f1
            | _ ->
                match x1 / (D dx y2) with
                | Number _ as n -> substitute n y2 f2
                | _ -> integral dx innerExpr
        | _ -> integral dx innerExpr

    match expr with
    | IsIntegral(f, dx) -> inner dx f
    | Product [ IsIntegral(f, dx); a ] 
    | Product [ a; IsIntegral(f, dx) ] -> a * inner dx f
    | f -> f
  
let uSubstitutionSteps expr =
    let usub = symbol "u_{sub}"
    let trace = StepTrace(sprintf "$%s$" (Expression.toFormattedString expr))
    let failtrace = StepTrace(sprintf "$%s$" (Expression.toFormattedString expr))
    let substitute n y (f : FuncType) =
        let f' = f.WrapExpression usub
        match integratePartialRes usub f' with
        | res, true ->  
            trace.Add("And: ${0}$", [integral usub f' <=> res])
            n * replaceSymbol y usub res, trace
        | res, false ->  
            failtrace.Add(integral usub f' <=> res)
            res, failtrace

    let inner dx innerExpr =
        match innerExpr with
        | Product [ AsFunction(f1, y1) as x1; AsFunction(f2, y2) as x2 ] ->
            failtrace.Add ("${0}$ is not proportional to ${1}={2}$",fmt, 
                            [x2; diff dx y1;D dx y1])
            match x2 / (D dx y1) with
            | Number _ as n ->
                trace.Add
                  ("${0}$. Therefore ${1}$ and ${2} \\propto {3}$",
                    [|  usub <=> y1 |> string;
                        diff dx usub <=> D dx y1 |> string;
                        fmt (D dx y1) ;
                        fmt x2|])  
                sprintf "Allowing rewrite: $%sd%s = %sd%s$" (fmt n)
                    (fmt usub)
                    (fmt ((D dx y1) * n))
                    (fmt dx) |> trace.Add  
                trace.Add("Container function: " + string f1) 
                substitute n y1 f1
            | _ ->
                failtrace.Add ("${0}$ is not proportional to ${1}={2}$", fmt, 
                                [x1; diff dx y2; D dx y2])
                match x1 / (D dx y2) with
                | Number _ as n ->
                    trace.Add
                     ("${0}$. Therefore ${1}$ and ${2} \\propto {3}$",
                     [| usub <=> y2 |> string
                        diff dx usub <=> D dx y2 |> string
                        fmt (D dx y2) 
                        fmt x1|])  
                    sprintf "Allowing rewrite: $%sd%s = %sd%s$" (fmt n)
                        (fmt usub)
                        (fmt ((D dx y2) * n))
                        (fmt dx) |> trace.Add 
                    trace.Add("Container function: " + string f2)
                    substitute n y2 f2
                | _ -> integral dx innerExpr, failtrace
        | _ -> integral dx innerExpr, failtrace

    match expr with
    | IsIntegral(f, dx) -> inner dx f
    | Product [ IsIntegral(f, dx); a ] | Product [ a; IsIntegral(f, dx) ] ->
        let r, tr = inner dx f in a * r, tr
    | f -> f, failtrace

 
let rewriteIntegralAsExpectation =
    function
    | FunctionN(Function.Integral, Product l :: _) as f ->
        maybe {
            let! p = List.tryFind (function
                         | FunctionN(Probability, _) -> true
                         | _ -> false) l
            return FunctionN(Function.Expectation,
                             [ (Product l) / p; p ])
        }
        |> Option.defaultValue f
    | f -> f
    
let expectationsDistribution = function
    | IsExpectation (_, px) -> px
    | _ -> Undefined
    
let expectationsProbInner = function
    | IsExpectation (_, IsProb x) -> x
    | _ -> Undefined

let innerProb = function
    | IsProb x -> x
    | _ -> Undefined

let rewriteExpectationAsIntegral = function
    | FunctionN(Function.Expectation, [ expr; distr ]) ->
        let dx =
            match Structure.first Expression.isVariable (innerProb distr) with
            | Some e -> [ e ] | None -> []
        FunctionN(Function.Integral, (distr * expr) :: dx)
    | f -> f    

let changeOfVariable dy = function 
    | IsIntegral(f,_) -> integral dy f
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

module Units =
    let integrate (dx:Units) (fx : Units) = 
        Units (evalIntegral (integral dx.Quantity fx.Quantity), fx.Unit, fx.AltUnit + " " + dx.AltUnit) * dx

    let definiteIntegrate a b (dx:Units) (fx : Units) = 
        Units (evalDefiniteIntegral (defintegral dx.Quantity a b fx.Quantity), fx.Unit, fx.AltUnit + " " + dx.AltUnit) * dx