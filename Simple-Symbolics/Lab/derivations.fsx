#load "solving.fsx"

open MathNet.Symbolics
open Core
open Solving

let deriveTrivialEqualitiesSingle (e1, eq) =
    [ yield Equation(e1, eq)
      for var in findVariablesOfExpression eq do
          match reArrangeEquation0 true var (eq, e1) with
          | Identifier _ as var, req ->
              yield Equation(var, Algebraic.simplify true req)
          | _ -> () ]

let deriveTrivialEqualities eqs =
    let removeRepeats (eqlist : _ list) =
        if eqlist.Length = 0 then eqlist
        else
            eqlist
            |> List.groupBy (fun (e : Equation) -> e.Equalities)
            |> List.map (fun (_, a) -> a.[0])

    let rec loop n (eqs : Equation list) =
        let deqs =
            [ for eq in eqs do
                  yield! deriveTrivialEqualitiesSingle eq.Equalities.Head ]

        let deriveds = Hashset deqs |> Seq.toList
        if n = 1 then deriveds
        else loop (n + 1) deriveds

    loop 0 eqs |> removeRepeats

let genEqualitiesList (eqs : Equation list) =
    [ for e in eqs do
          yield! e.Equalities ]
    |> Hashset
    |> Seq.toList

let deriveAndGenerateEqualities = deriveTrivialEqualities >> genEqualitiesList

let solveProductForm e =
    function
    | (Product l) as p ->
        l
        |> List.map (fun e2 ->
               let r = (p * (1 / e2)) / e
               if Expression.isNegativePower e2 then r, 1 / e2
               else 1Q / r, e2)
    | _ -> []

let deriveEqualitiesFromProduct es =
    es
    |> List.collect (fun (e1, e2) ->
           (e1, e2) :: solveProductForm e1 e2
           |> List.map Equation
           |> genEqualitiesList)
