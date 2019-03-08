
#load "Core.fsx"

open MathNet.Symbolics
open System.Numerics
open MathNet.Numerics
open MathNet
open Operators
open Core
open Core.Vars


let integratePolynomExpr m n e = e**(n+1Q)/(m * (n+1Q)) 
let isLinear x f = Polynomial.isPolynomial x f && (Polynomial.degree x f).ToFloat() = 1.
let intFuncStraight = function
    | Function(Cos, (x)) -> Function(Sin, x)
    | Function(Sin,x) -> -Function(Cos, x)
    | Function(Tan,x) -> -ln(cos x)
    | Function(Ln, x) -> x * Function(Ln, x) - x
    | Function(Log, x) -> x * Function(Log, x) - x
    | Function(Exp, x) -> Function(Exp,x)
    | _ -> failwith "function unmet"
 
let extractLinearComponent x ex =
    let e' = Polynomial.collectTerms x ex
    let l = Algebraic.summands e'
    let matches, _ = List.partition (containsVar x) l
      
    match matches with 
    | [Identifier (Symbol _) as x'] when x = x' -> 1Q, e'
    | [Product l] -> match List.filter ((<>) x) l with
                      | [t] -> t, e'
                      | _ -> failwith "Could not extract terms in power"
    | _ -> failwith "Power attempt failed, not a product"
 

let linearSquared combinator = combinator (function | Power(e, n) when n = 2Q && isLinear x e -> true | _ -> false)  

type IntegrationResult =
      | Suceeded of Expression
      | Partial of Success:Expression * Defer:Expression
      | Deferred of Expression

let justSuccess = function | Suceeded e -> e | _ -> failwith "could not extract"
      
let integrateSimplePartial x f =  
    let rec iter = function 
    | Number _ as n -> Suceeded(n * x) 
    | Identifier (Symbol _) as vx -> if vx = x then Suceeded(vx ** 2/2)  else Suceeded(vx * x) 
    | f when f = 1/(1 + x ** 2) -> Suceeded(arctan x) 
    | Power(Sum l, neg1) as f when neg1 = -1Q && linearSquared List.exists l -> 
        let ex, l' = linearSquared List.partition l
        let n = Sum l'
        match ex with 
        | [Power(e, _)] ->
            let m, _ = extractLinearComponent x e
            let fx = arctan (e / (sqrt n)) / (m * sqrt n) |> Algebraic.simplify true
            Suceeded fx 
        |_ -> Deferred f
    | f when f = 1/(sqrt (1 - x ** 2)) -> Suceeded(arcsin x)
    | Power(e, n) as p when not (containsVar x e) && not(containsVar x n) ->  Suceeded(p * x)
    | Power(e, n) as p when not (containsVar x e) && (containsVar x n) && isLinear x n ->  
           Suceeded(p / (fst (extractLinearComponent x n)  * ln(e)))
    | Power(e, n) as f when not (containsVar x e) && (containsVar x n) -> printfn "Power nolinear in x, fail" ; Deferred f
    | Power(e, n) when n = -1Q && e <> 0Q && isLinear x e -> Suceeded(Function(Ln , e)/fst (extractLinearComponent x e)) 
    | Power (Identifier _ as y, n) when x = y && n <> -1Q -> Suceeded((x ** (n + 1)) / (n + 1))
    | poly when Polynomial.isMonomial x poly ->
        let k, mono = Algebraic.separateFactors x poly
        match (iter mono) with
         | Suceeded fx  -> Suceeded(k * fx) 
         | _ -> failwith "unexpected state in integrate monomial"         
    | Power(Sum _ as e, n) when isLinear x e && n <> -1Q -> 
        let t, e' = extractLinearComponent x e
        Suceeded(integratePolynomExpr t n e')
    | Power(e, n) as poly when Polynomial.isPolynomial x e && n <> -1Q -> 
        Suceeded
         (poly |> Algebraic.expand  
               |> Algebraic.summands 
               |> List.map (iter >> justSuccess)
               |> Sum)
    | Function(f, (Identifier (Symbol _) as y)) when x <> y -> Suceeded(x * Function(f, y))
    | Function(f, (Number _ as n)) -> Suceeded(x * Function(f, n))
    | Function(_, (Identifier (Symbol _))) as f -> Suceeded (intFuncStraight f)
    | Function(_, ex) as f when isLinear x ex ->  
        Suceeded((intFuncStraight f) / fst(extractLinearComponent x ex))
    | Sum l -> 
      let calculated, deferred =
          List.fold (fun (sums,ins) r -> 
               match r with 
               | Suceeded g -> g + sums, ins
               | Partial(Success = g; Defer = f) -> g + sums, f + ins
               | Deferred f -> sums, ins + f) (0Q, 0Q) (List.map iter l) 
      Partial(calculated, deferred)
    | Product _ as e -> 
        let k, e' = Algebraic.separateFactors x e  
        if k = 1Q then printfn "Separating factors, no x found."; Deferred e
        else match (iter e') with
             | Suceeded good -> Suceeded(k * good) 
             | Partial(good, fail) -> Partial((k * good), fail)
             | Deferred fail -> Partial(k,fail)             
    | f when not(containsVar x f) -> Suceeded (x * f)    
    | f -> printfn "Can't integrate this %s" (f.ToFormattedString()); Deferred f
    iter f
     
let rec integrateSimple x = function 
    | Number _ as n -> n * x 
    | Identifier (Symbol _) as vx -> if vx = x then vx ** 2/2 else vx * x
    | f when f = 1/(1 + x ** 2) -> arctan x
    | Power(Sum l, neg1) when neg1 = -1Q && linearSquared List.exists l -> 
        let ex, l' = linearSquared List.partition l
        let n = Sum l'
        match ex with 
        | [Power(e, _)] ->
            let m, _ = extractLinearComponent x e
            arctan (e / (sqrt n)) / (m * sqrt n) |> Algebraic.simplify true
        | _ -> failwith "err"
    | f when f = 1/(sqrt (1 - x ** 2)) -> arcsin x
    | Power(e, n) as p when not (containsVar x e) && not(containsVar x n) ->  p * x
    | Power(e, n) as p when not (containsVar x e) && (containsVar x n) && isLinear x n ->  p / (fst (extractLinearComponent x n)  * ln(e))
    | Power(e, n) when not (containsVar x e) && (containsVar x n) -> failwith "Power nolinear in x, fail" 
    | Power(e, n) when n = -1Q && e <> 0Q && isLinear x e -> Function(Ln , e)/fst (extractLinearComponent x e) 
    | Power (Identifier _ as y, n) when x = y && n <> -1Q -> (x ** (n + 1)) / (n + 1) 
    | poly when Polynomial.isMonomial x poly ->
        let k, mono = Algebraic.separateFactors x poly
        k * integrateSimple x mono
    | Power(Sum _ as e, n) when isLinear x e && n <> -1Q -> 
        let t, e' = extractLinearComponent x e
        integratePolynomExpr t n e'     
    | Power(e, n) as poly when Polynomial.isPolynomial x e && n <> -1Q -> 
          poly |> Algebraic.expand  
               |> Algebraic.summands 
               |> List.map (integrateSimple x)
               |> Sum
    | Function(f, (Identifier (Symbol _) as y)) when x <> y -> x * Function(f, y)
    | Function(f, (Number _ as n)) -> x * Function(f, n)
    | Function(_, (Identifier (Symbol _))) as f -> intFuncStraight f   
    | Function(_, ex) as f when isLinear x ex ->  
        (intFuncStraight f) / fst(extractLinearComponent x ex)
    | Sum l -> Sum(List.map (integrateSimple x) l)
    | Product _ as e -> 
        let k, e' = Algebraic.separateFactors x e  
        if k = 1Q then failwith "Separating factors, no x found. Aborting."
        else k * integrateSimple x e' 
    | f when not(containsVar x f) -> x * f
    
    | x -> failwith "Can't integrate this"

type Integral(fx, x:Expression) =
    let expr = Function(Function.Integral, fx)
    member t.Expression = expr
    member t.Compute() = integrateSimple x fx
    override t.ToString() = 
       sprintf @"\displaystyle \int %s d%s" (fx.ToFormattedString()) (x.ToFormattedString())
 
integrateSimple x (1/((a * x + x + b)**2 + 1)) |> Infix.format
integrateSimple x (1/(1 * (a * x + x + b)**2 + b)) |> Infix.format
integrateSimple x (1/(((a+2) * x + b + c + x)**2 + c + y)) |> Infix.format //Caveats
integrateSimple x (1/((a * x+b)**2 + 0)) |> Infix.format 
integrateSimple x (1/((1 + x))) |> Infix.format
integrateSimple x (5Q ** (3*x + 1))|> Infix.format
integrateSimple x (exp x)|> Infix.format
integrateSimple x (exp (x+1 + a * x))|> Infix.format
integrateSimple x (log (x+1 + a * x))|> Infix.format
integrateSimple x ((a * x + b * x + 3) ** 2) |> Infix.format 
integrateSimple x ((x ** 2 * a * b) ** 2)    |> Infix.format  
integrateSimple x (1/sqrt x) |> Infix.format
integrateSimple x (1/sqrt(x+1)) |> Infix.format 
integrateSimple x (cos (x+1)) |> Infix.format 
integrateSimple x (1/(3*x+1)) |> Infix.format
integrateSimple x ((a * x + 3) ** 2) |> Infix.format 
integrateSimple x ((a * x ** 2 + 3) ** 2)  |> Infix.format  
integrateSimple x ((a * x + b * x ** 2 + 3) ** 2) |> Infix.format 
integrateSimple x (1/x) |> Infix.format
((x ** 2 * a + 3) ** 2) |> Algebraic.expand |> integrateSimple x |> Infix.format 
integrateSimple x (1/(x+1)**a) |> Infix.format  //Caveats
integrateSimple t a |> integrateSimple t |> Infix.format
integrateSimple t (a * t + v0) |> Infix.format


csc(2*x + 1) * cot(2*x + 1 ) |> Trigonometric.separateFactors // |> Infix.format
///////////BROKE
//integrateSimple x (1/( sqrt(1 - 16 * x **2) )) |> Infix.format

//integrateSimple x (1/((3 * (a * x)**2 + 1))) |> Infix.format 
//integrateSimple x (1/((a * x)**2 + 1) ) |> Infix.format 
//integrateSimple x (a * x * cos x) |> Infix.format     
//integrateSimple x (1/(3*x**2+1)) |> Infix.format
//integrateSimple x (1/cos(x))|> Infix.format

//integrateSimplePartial x (5 * x + 1/cos(x))
