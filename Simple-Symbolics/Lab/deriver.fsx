#I @"C:\Users\Admin\Documents\Visual Studio 2017\Projects\Hansei\Hansei\bin\Release\net45"
#r "prelude.dll"
#r "hansei.dll"

#load "solving.fsx"
open System.Collections.Generic

open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics
open MathNet.Symbolics
open Solving



let rec findVariablesOfExpression = function 
   | Identifier _ as var -> [var]
   | Power(x, n) -> findVariablesOfExpression x @ findVariablesOfExpression n
   | Product l 
   | Sum     l -> List.collect findVariablesOfExpression l
   | Function (_, x) -> findVariablesOfExpression x   
   | _ -> []

let feq e1 eq = 
    [ yield Equation(e1,eq)
      for var in findVariablesOfExpression eq do 
       match reArrangeEquation var (eq, e1) with
       | Identifier _ as var, req -> yield Equation(var, req) 
       | _ -> () ]


let ``P(A|B)`` = Operators.symbol "P(A|B)"
let ``P(A ∩ B)`` = Operators.symbol "P(A ∩ B)"
let ``P(B)`` = Operators.symbol "P(B)"

 
feq ``P(A|B)`` (``P(A ∩ B)``/``P(B)`` ) 
        
