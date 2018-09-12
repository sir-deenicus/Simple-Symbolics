
#load "Core.fsx"

open MathNet.Symbolics
open System.Numerics
open MathNet.Numerics
open MathNet
open Operators
open Core
open Core.Vars


let rec hasNesting = function 
      | Product l -> List.exists hasNesting l 
      | Power _ -> true
      | Sum _ -> true
      | Function _ -> true
      | _ -> false

let integratePolynomExpr x m n e = e**(n+1Q)/(m * (n+1Q)) 
let isLinear x f = (Polynomial.degree x f).ToFloat() = 1.
let intFuncStraight = function
    | Function(Cos, (x)) -> Function(Sin, x)
    | Function(Sin,x) -> -Function(Cos, x)
    | Function(Ln, x) -> x * Function(Ln, x) - x
    | Function(Log, x) -> x * Function(Log, x) - x
    | Function(Exp, x) -> Function(Exp,x)
    | _ -> failwith "function unmet"

let rec integrateSimple x = function
    | Power(e, n) when n = -1Q && e <> 0Q -> Function(Ln , e) //incomplete
    | Power(Sum _ as e, n) -> 
        let e' = Polynomial.collectTerms x e
        let l = Algebraic.summands e'
        let matches, _ = List.partition (containsVar x) l
        match matches with 
        | [Product l] -> match List.filter ((<>) x) l with
                         | [t] -> integratePolynomExpr x t n e'
                         | _ -> failwith "Could not extract terms in power"
        | _ -> failwith "Power attempt failed, not a product"
    
    | Power(e, n) when not(hasNesting e) -> integratePolynomExpr x 1Q n e
    | Sum l -> 
        Sum(List.map (integrateSimple x) l )
    | Number _ as n -> n * x
    | Function(f, (Identifier (Symbol _) as y)) when x <> y -> x * Function(f, y)
    | Function(f, (Identifier (Symbol _))) as f' -> intFuncStraight f'   
    | Function(f, ex) as f' when isLinear x ex -> 
        let e' = Polynomial.collectTerms x ex
        let l = Algebraic.summands e'
        let matches, _ = List.partition (containsVar x) l
        let m =   
            match matches with 
            | [Identifier (Symbol _) as x'] when x = x' -> 1Q
            | [Product l] -> match List.filter ((<>) x) l with
                              | [t] -> t
                              | _ -> failwith "Could not extract terms in power"
            | _ -> failwith "Power attempt failed, not a product"

        (intFuncStraight f') / m
    | Function(Exp, _) as e -> e //incomplete
    | Identifier (Symbol _) as vx -> if vx = x then vx ** 2/2 else vx * x
    | Product _ as e -> 
        let k, e' = Algebraic.separateFactors x e  
        if k = 1Q then failwith "Separating factors, no x found. Aborting."
        else k * integrateSimple x e' 
    | _ -> failwith "Can't integrate this"
 
(log 2Q).ToFloat()
log10 2.
 

integrateSimple x (exp (x+1 + a * x))|> Infix.format
integrateSimple x (log (x+1 + a * x))|> Infix.format
integrateSimple x (1/cos(x))|> Infix.format
integrateSimple x ((a * x + b * x + 3) ** 2) |> Infix.format 
integrateSimple x ((x ** 2 * a * b) ** 2)    |> Infix.format  
integrateSimple x (1/sqrt x) |> Infix.format
integrateSimple x (1/x) |> Infix.format

integrateSimple t a |> integrateSimple t |> Infix.format

integrateSimple t (a * t + v0) |> Infix.format
///////////BROKE
integrateSimple x (a * x * cos x) |> Infix.format     
integrateSimple x (1/sqrt(x+1)) |> Infix.format
integrateSimple x ((a * x + b * x ** 2 + 3) ** 2) |> Infix.format 
integrateSimple x ((x ** 2 * a + 3) ** 2)  |> Infix.format  

integrateSimple x (cos (x+1)) |> Infix.format  
integrateSimple x (1/(3*x+1)) |> Infix.format

integrateSimple x (1/(x+1)**n) |> Infix.format 