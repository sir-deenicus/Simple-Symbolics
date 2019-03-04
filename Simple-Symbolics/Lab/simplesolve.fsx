//HIDDENX
//#I @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45"
#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\Lab"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45\Prelude.dll"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45\Hansei.Core.dll"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45\Hansei.dll"
//#r "prelude.dll"
//#r "hansei.core.dll"
//#r "hansei.dll"
#load "derivations.fsx"

open System.Collections.Generic
open Hansei
//open Solving
open Hansei.Core
open Hansei.Continuation
open MathNet.Symbolics
open Core.Vars
open Core
open MathNet.Numerics
open Prelude.Common
open System
open Hansei.Core.Distributions
open Prelude.StringMetrics
open Derivations

let eff = symbol "eff"
let tc = symbol "T_C"
let th = symbol "T_H"
let W = symbol "W"
let qh = symbol "Q_H"
let qc = symbol "Q_c"
let eq1 = eff <=> 1 - tc / th
let eq2 = W <=> qh - qc

let knowns =
    deriveAndGenerateEqualities [ eff <=> 1 - tc / th
                                  W <=> qh - qc
                                  qc <=> (1 - eff) * qh ] 

let vars =
    [ tc, 350.
      qc, 6.3e3
      th, 650. ]

module List =
    let mapFilter f filter xs =
        [for x in xs do if filter x then yield f x ]      

let candidates =        
    knowns
    |> List.filter
           (fun (_, e) -> vars |> List.exists (fun (v, _) -> Core.containsVar v e))
 

[for (e,e2) in candidates do
    match Expression.evaluateFloat vars e2 with 
    | None -> ()
    | Some v -> yield e, v.]
    
