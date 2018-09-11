
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
    | Function(Cos, (Identifier (Symbol _) as y)) -> Function(Sin, y)
    | Function(Sin, (Identifier (Symbol _) as y)) -> -Function(Cos, y)
    | Function(Exp, _) as e ->  e //incomplete
    | Identifier (Symbol _) 
    | Product _ as e -> 
        let k, e' = Algebraic.separateFactors x e  
        if k = 1Q then failwith "Separating factors, no x found. Aborting."
        else k * integrateSimple x e' 
    | _ -> failwith "Can't integrate this"
   

let rr = integrateSimple x ( (x ** 2 + 3 ) ** 2 ) 

integrateSimple x (5 * x) |> Infix.format

integrateSimple t (a) |> integrateSimple t |> Infix.format

rr |> Infix.format  
     
     