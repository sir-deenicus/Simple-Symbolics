#load "solving.fsx"

open MathNet.Symbolics
open Core
open Solving

let deriveTrivialEqualitiesSingle(e1,eq) =
    [yield Equation(e1,eq)
     for var in findVariablesOfExpression eq do
         match reArrangeEquation0 true var (eq,e1) with
         | Identifier _ as var,req -> yield Equation(var,req)
         | _ -> ()]

let deriveTrivialEqualities(eqs: Equation list) =
    let deqs =
        [for eq in eqs do
             yield! deriveTrivialEqualitiesSingle eq.Equalities.Head]
    Hashset deqs |> Seq.toList

let genEqualitiesList(eqs: Equation list) =
    [for e in eqs do
         yield! e.Equalities]

let deriveAndGenerateEqualities = deriveTrivialEqualities >> genEqualitiesList     