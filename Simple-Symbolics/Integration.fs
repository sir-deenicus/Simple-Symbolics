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
open NumberProperties
open Summation
open MathNet.Symbolics.Core
open Expression
open Equations
 
module Expression =
    let isIntegral = function IsIntegral _ -> true | _ -> false

let integratePolynomExpr m n e = e ** (n + 1Q) / (m * (n + 1Q))
 
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
        | Power(e, n) when n = 2Q && isLinearIn x e -> true
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
                        |> Expression.simplify 
                    Succeeded fx
                | _ -> Deferred (f, false)
            | _ -> Deferred (f, false)
        | f when f = 1 / (sqrt (1 - x ** 2)) -> Succeeded(arcsin x)
        | Power(e, n) as p when not (containsVar x e) && not (containsVar x n) ->
            Succeeded(p * x)
        | Power(e, n) as p when not (containsVar x e) && (containsVar x n)
                                && isLinearIn x n ->
            Succeeded(p / (fst (extractLinearComponent x n) * ln (e)))
        | Power(e, n) as f when not (containsVar x e) && (containsVar x n) ->
            //printfn "Power nonlinear in x, fail"
            Deferred (f,false)
        | Power(e, n) when n = -1Q && e <> 0Q && isLinearIn x e ->
            Succeeded(Function(Ln, abs e) / fst (extractLinearComponent x e))
        | Power(Identifier _ as y, n) when x = y && n <> -1Q ->
            Succeeded((x ** (n + 1)) / (n + 1))
        | poly when Polynomial.isMonomial x poly ->
            let k, mono = Algebraic.separateFactors x poly
            match (iter mono) with
            | Succeeded fx -> Succeeded(k * fx)
            | _ -> failwith "unexpected state in integrate monomial"
        | Power(Sum _ as e, n) when isLinearIn x e && n <> -1Q ->
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
        | Function(_, ex) as f when isLinearIn x ex ->
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
      
let internal freshConstant varname e =
    let vs = Expression.findVariables e
    let varname = defaultArg varname "C"
    let var = symbol varname
    let cvs =
        vs
        |> Seq.filter (function
            | ExpressionPatterns.IsSymbolVar s -> s.Contains varname
            | _ -> false)

    let i = Seq.length cvs
    var[(i + 1)]

     
let integratePartialResAux varname trackConstants x e =
    match (integrateSimplePartial x e) with 
    | Partial(s, def, true) -> s + def, false
    | Partial(s, def, false) -> s * (integral x def), false
    | Succeeded e -> (if not trackConstants then e else e + freshConstant varname e), true
    | Deferred (e,true) -> e, false
    | Deferred (e,false) -> integral x e, false

let integratePartialRes x e = integratePartialResAux None false x e

let integratePartial x e = fst(integratePartialRes x e)
 
let evalIntegral =
    function
    | IsIntegral(f, dx) -> integratePartial dx f
    | f -> f  
    
let evalIntegralC_vname varname =
    function
    | IsIntegral(f, dx) -> fst(integratePartialResAux varname true dx f)
    | f -> f 

let evalIntegralC = evalIntegralC_vname None

let evalDefiniteIntegral =
    function
    | IsDefiniteIntegral(f, dx,a,b) as fn -> 
        match integratePartialRes dx f with
        | (_, false) -> fn
        | (e, true) -> Expression.replaceWith b dx e - Expression.replaceWith a dx e
    | f -> f 
 
let evalDefiniteIntegralUsing integrator = function
    | IsDefiniteIntegral(f, dx,a,b) as fn ->
        match integrator f with
            | IsIntegral _ -> fn
            | e -> Expression.replaceWith b dx e - Expression.replaceWith a dx e
    | f -> f
    
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
           | Some ex -> if Structure.width ex > Structure.width res then res, false else ex,false
        else res, true
    match expr with
    | IsIntegral(Product [a;b],dx) -> 
        let res, ok = doIntegrateByParts None dx a b
        if ok then res
        else doIntegrateByParts (Some res) dx b a |> fst
    | IsIntegral(f,dx) -> integrateByParts (integral dx (Product [1Q; f]))
    | f -> f  

  
let uSubstitution expr =
    let usub = symbol "u_{sub}"

    let substitute n y (f : FuncType) =
        let f' = f.WrapExpression usub
        match integratePartialRes usub f' with
        | res, true -> n * replaceSymbolWith y usub res
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
            n * replaceSymbolWith y usub res, trace
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


module Integral =
    let inner = function IsIntegral(f,_) | IsDefiniteIntegral(f,_,_,_) -> f | f -> f
    
    let integratingVar = function 
        | IsIntegral(_,dx) 
        | IsDefiniteIntegral(_,dx,_,_) -> Some dx 
        | _ -> None
        
    let toDefinite a b = function
        | IsIntegral (f, dx) -> defintegral dx a b f
        | f -> f
        
    /// <summary>
    /// Given an integral expression, rewrites it as sums.
    /// </summary>
    /// <param name="usedelta">If true, uses delta notation for the discretized variable of integration.</param>
    /// <param name="expr">The integral expression to rewrite.</param>
    /// <returns>The rewritten expression.</returns>
    let rewriteAsSum usedelta expr = 
        let dxtodelta dx = 
            let delta = if Utils.InfixFormat = "Infix" then "Δ" else "\\Delta "
            V(delta + symbolString dx)
        let rec inner = function
            | IsIntegral((IsIntegral _ as innerexpr), dx) -> 
                let innerexpr' = inner innerexpr   
                FunctionN(SumOver, [Product[yield innerexpr'; if usedelta then yield dxtodelta dx]; dx])

            | IsIntegral(x, dx) -> 
                FunctionN(SumOver, [Product[yield x; if usedelta then yield dxtodelta dx] |> Expression.simplifyLite ; dx])

            | IsDefiniteIntegral((IsIntegral _ as innerexpr), dx, a, b) ->
                let innerexpr' = inner innerexpr   
                FunctionN(SumOver, [Product[yield innerexpr'; if usedelta then yield dxtodelta dx]; dx; a; b])

            | IsDefiniteIntegral(x, dx, a, b) ->
                FunctionN(SumOver, [Product[yield x; if usedelta then yield dxtodelta dx] |> Expression.simplifyLite ; dx; a; b])

            | f -> f
        inner expr          
                       
    let rewriteAsExpectation =
        function
        | FunctionN(Integral, Product l :: _) as f ->
            maybe {
                let! p =
                    List.tryFind (function
                    | FunctionN(Probability, _) -> true
                    | _ -> false) l

                return FunctionN(Expectation, [ (Product l) / p; p ])
            }
            |> Option.defaultValue f
        | f -> f
     
    let ofExpectation = function
        | FunctionN(Expectation, [ expr; distr ]) as ex ->
            //need to handle nesting
            let dxs = Prob.getVariable distr
            //dxs is either a tuple or a single variable
            match dxs with
            | Some (Tupled (v::vars)) -> 
                vars 
                |> List.fold (fun expr dx -> integral dx expr) (integral v (distr * expr))
            | Some (Identifier _ as dx) -> integral dx (distr * expr)
            | _ -> ex 
        | f -> f    
         
    let rewriteGammaAsIntegral = function 
        | Function(Gamma, z) ->  
            defintegral t 0 Symbolics.Operators.infinity ((t**(z-1.)) * exp(-t))
        | x -> x

    let cancelDerivative = function
    | IsIntegral(IsDerivative(_, f, dx), dx') when dx = dx' -> f
    | x -> x

    let makeDefinite a b = function
        | IsIntegral(f, dx) -> defintegral dx a b f
        | f -> f

    let ofDefinite = function
        | IsDefiniteIntegral(f, dx, _, _) -> integral dx f
        | f -> f
 
///The module for computing entropy and related quantities, the N stands for Nested as it expands distributions of multiple variables into nested integrals
module EntropyN = 
    ///<summary>Computes the relative entropy or KL divergence between two probability distributions. D(p||q) = \int p(x) log(p(x)/q(x)) dx</summary>
    /// <param name="px">The first probability distribution</param>
    /// <param name="qx">The second probability distribution</param>
    /// <returns>The relative entropy between the two distributions</returns>
    let relativeEntropy px qx =
        //KL divergace D(p||q) = \int p(x) log(p(x)/q(x)) dx
        let calc px qx =
            //we need to integrate over all variables in px
            match Prob.getVariable px with
            | Some(Tupled(v :: vs)) -> 
                //we also need to marginalize over all variables in qx
                let qxvars =    
                    match Prob.getVariable qx with 
                    | Some (Tupled vs) -> vs
                    | Some v -> [v]
                    | None -> []
                //remove all variables in px from qx
                let qxvars = 
                    let pxset = Hashset (v::vs)
                    qxvars |> List.filter (pxset.Contains >> not)

                vs @ qxvars
                |> List.fold (flip integral) (integral v (px * log (px / qx)))
            | Some v -> integral v (px * log (px / qx))
            | None -> undefined
        match px, qx with
        | IsProb _ as px, (IsProb _ as qx) -> 
            calc px qx
        | px, (Product l as qx) when List.forall Prob.isProb l -> 
            calc px qx
        | (Product l as px), qx when List.forall Prob.isProb l -> 
            calc px qx 
        | _ -> undefined

    ///<summary>
    /// Computes the mutual information between X and Y. I(X;Y) = \int \int p(x,y) log(p(x,y)/(p(x)p(y))) dx dy
    /// </summary>
    /// <param name="px">The marginal distribution of X</param>
    /// <param name="py">The marginal distribution of Y</param>
    /// <param name="pxy">The joint distribution of X and Y</param>
    /// <returns>The mutual information between X and Y</returns>
    let mutualInformation px py pxy =
        //I(X;Y) = \int \int p(x,y) log(p(x,y)/(p(x)p(y))) dx dy
        //It is also the KL divergence between the joint distribution and the product of the marginals
        relativeEntropy pxy (px * py)

    ///<summary>
    /// Computes the (discrete) conditional entropy of Y given X. H(Y|X) = \sum_x \sum_y p(x,y) log(p(x,y)/p(x))
    /// </summary>
    /// <param name="px">The marginal distribution of X</param>
    /// <param name="py">The marginal distribution of Y</param>
    /// <returns>The conditional entropy of Y given X</returns>
    let conditionalEntropy cpyx = 
        //P(X|Y) = P(X,Y)/P(Y)
        //H(Y|X) = \sum_x \sum_y p(x,y) log(p(x,y)/p(x)) 
        match cpyx with
        | IsCondProb _ ->
            let jpy = Prob.condToJoint p   
            match Prob.getVariable cpyx with
            | Some(Tupled(v :: vs)) ->    
                vs  
                |> List.fold (fun sums varx -> Summations.Σ(varx, sums)) (Summations.Σ(v, Rational.numerator jpy * log jpy))
            | Some v -> Summations.Σ(v, Rational.numerator jpy * log jpy)
            | None -> undefined   
        | _ -> undefined
 
    let entropy p = 
        //H(X) = -\sum_x p(x) log(p(x))
        match p with
        | IsProb _ as p -> 
            match Prob.getVariable p with
            | Some(Tupled(v :: vs)) ->  
                vs
                |> List.fold (fun sums varx -> Summations.Σ(varx, sums)) (Summations.Σ(v, p * log p))
            | Some v -> Summations.Σ(v, p * log p)
            | None -> undefined   
        | _ -> undefined

/// A module for computing the entropies of distributions. It does not perform nesting of integrals
module Entropy =
    let relativeEntropy px qx = 
        //KL divergace D(p||q) = \int p(x) log(p(x)/q(x)) dx
        match px, qx with
        | (IsProb _) as px, (IsProb _ as qx) -> 
            match Prob.getVariable px with
            | Some v -> integral v (px * log (px / qx))
            | None -> undefined
        | (Definition(IsProb _ as px, inner, s1), Definition(IsProb _ as qx, inner2, s2)) -> 
            match Prob.getVariable px with
            | Some v -> Definition(integral v (px * log (px / qx)), integral v (inner * log (inner / inner2)), $"Relative entropy of {s1} and {s2}")
            | None -> undefined
        | _ -> undefined
            
    let mutualInformation px py pxy =
        //I(X;Y) = \int \int p(x,y) log(p(x,y)/(p(x)p(y))) dx dy
        //It is also the KL divergence between the joint distribution and the product of the marginals
        relativeEntropy pxy (px * py)

    ///<summary>
    /// Computes the (discrete) conditional entropy of Y given X. H(Y|X) = \sum_x \sum_y p(x,y) log(p(x,y)/p(x))
    /// </summary>
    /// <param name="cpyx">The conditional distribution of Y given X</param>
    /// <returns>The conditional entropy of Y given X</returns>
    let conditionalEntropy cpyx =
        //H(Y|X) = \sum_x \sum_y p(x,y) log(p(x,y)/p(x))
        match cpyx with
        | IsCondProb _ ->
            let jp = Prob.condToJoint cpyx
            match Prob.getVariable cpyx with
            | Some v -> Summations.Σ(v, Rational.numerator jp * log jp)
            | None -> undefined  
        | _ -> undefined

    ///<summary>
    /// An alternate way of computing the (discrete) conditional entropy of Y given X. H(Y|X) = \sum_x \sum_y p(x,y) log(p(x,y)/p(x))
    /// </summary>
    /// <param name="jpxy">The joint distribution of X and Y</param>
    /// <param name="py">The marginal distribution of Y</param>
    /// <param name="px">The marginal distribution of X</param>
    /// <returns>The conditional entropy of Y given X</returns>
    let conditionalEntropy2 jpxy py px =
        //H(Y|X) = \sum_x \sum_y p(x,y) log(p(x,y)/p(x))
        match jpxy, py, px with
        | (IsProb _ as jpxy), (IsProb _ as py), (IsProb _ as px) ->
            match Prob.getVariable jpxy with 
            | Some v -> Summations.Σ(v, jpxy * log (jpxy / (px * py)))
            | None -> undefined   
        | Definition(IsProb _ as jpxy, jpinner, s1), Definition(IsProb _ as py, pyinner, s2), Definition(IsProb _ as px, pxinner, s3) ->
                match Prob.getVariable jpxy with 
                | Some v -> Definition(Summations.Σ(v, jpxy * log (jpxy / (px * py))), Summations.Σ(v, jpinner * log (jpinner / (pyinner * pxinner))), $"Conditional entropy of {s1} given {s2} and {s3}")
                | None -> undefined
        | _ -> undefined

    let entropy p = 
        //H(X) = -\sum_x p(x) log(p(x))
        match p with
        | IsProb _ as p -> 
            match Prob.getVariable p with
            | Some v -> Summations.Σ(v, p * log p)
            | None -> undefined   
        | Definition(IsProb _ as p, inner, s) -> 
            match Prob.getVariable p with
            | Some v -> Definition(Summations.Σ(v, p * log p), Summations.Σ(v, inner * log inner), $"Entropy of {s}")
            | None -> undefined   
        | _ -> undefined
            
module DefiniteIntegral = 
    let makeInDefinite = function
        | IsDefiniteIntegral(f, dx, _, _) -> integral dx f
        | f -> f

module Riemann =
    let ofIntegral = function 
        | IsDefiniteIntegral (f,dx,a,b) -> 
            let deltax = (b - a) / n
            let x_i = a + deltax * i

            summation i 1Q n (deltax * Expression.replaceWith x_i dx f)
            |> limit n Symbolics.Operators.infinity 
        | _ -> undefined
         

module Units =
    open Units
    let integrate (dx:Units) (fx : Units) = 
        Units (evalIntegral (integral dx.Quantity fx.Quantity), fx.Unit * dx.Unit, fx.AltUnit + " " + dx.AltUnit) 

    let definiteIntegrate a b (dx:Units) (fx : Units) = 
        Units (evalDefiniteIntegral (defintegral dx.Quantity a b fx.Quantity), fx.Unit * dx.Unit, fx.AltUnit + " " + dx.AltUnit) 

    type Units with
        static member Integrate(differential:Units,fn : Units) =
            integrate differential fn

        static member DefiniteIntegrate(start, stop, differential:Units, fn : Units) =
            definiteIntegrate start stop differential fn
