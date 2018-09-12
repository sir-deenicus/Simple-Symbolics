
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
     
let rec integrateSimple x = function 
    | Number _ as n -> n * x 
    | Identifier (Symbol _) as vx -> if vx = x then vx ** 2/2 else vx * x
    | Power(e, n) when n = -1Q && e <> 0Q && isLinear x e ->         
      Function(Ln , e)/fst (extractLinearComponent x e) 
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
    | Function(f, (Number _ as y)) -> x * Function(f, y)
    | Function(f, (Identifier (Symbol _))) as f' -> intFuncStraight f'   
    | Function(f, ex) as f' when isLinear x ex ->  
        (intFuncStraight f') / fst(extractLinearComponent x ex)
    | Sum l -> Sum(List.map (integrateSimple x) l)
    | Product _ as e -> 
        let k, e' = Algebraic.separateFactors x e  
        if k = 1Q then failwith "Separating factors, no x found. Aborting."
        else k * integrateSimple x e' 
    | f when not(containsVar x f) -> x * f 
    | _ -> failwith "Can't integrate this"

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

integrateSimple t a |> integrateSimple t |> Infix.format

integrateSimple t (a * t + v0) |> Infix.format

/////Caveats
integrateSimple x (1/(x+1)**a) |> Infix.format 
///////////BROKE

integrateSimple x (a * x * cos x) |> Infix.format     

integrateSimple x (1/(3*x**2+1)) |> Infix.format

integrateSimple x (1/cos(x))|> Infix.format


