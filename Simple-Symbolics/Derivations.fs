module MathNet.Symbolics.Derivations

open MathNet.Symbolics
open Core
open Solving 
open Prelude.Common
open NumberProperties
open Equations 

let deriveTrivialEqualities eqs =
    //try to solve for all variables in `right`
    let deriveTrivialEqualitiesSingle (left, right) =
        [ yield Equation(left, right)
          for var in Expression.findVariables right do
              match reArrangeExprEquation [] [] var (right, left) |> fst with
              | Identifier _ as var, req ->
                  yield Equation(var, Expression.simplify req)
              | _ -> () ]

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
        //solving sometimes introduces new forms that can be solved for. Two iterations should be enough.
        if n = 1 then deriveds
        else loop (n + 1) deriveds

    loop 0 eqs |> removeRepeats

let equalitiesToPairs (eqs : Equation list) =
    [ for e in eqs do
          yield! e.Equalities ]
    |> Hashset
    |> Seq.toList

let deriveAndGenerateEqualities = deriveTrivialEqualities >> equalitiesToPairs

let internal solveProductForm e =
    function
    | (Product l) as p ->
        l
        |> List.map (fun e2 ->
               let r = (p * (1 / e2)) / e
               if Expression.isNegativePower e2 then r, 1 / e2
               else 1Q / r, e2)
    | _ -> []

let deriveEqualitiesFromProduct (eqs:Equation list) =
    eqs
    |> List.collect (fun eq ->
           let (e1, e2) = eq.Definition
           (e1, e2) :: solveProductForm e1 e2
           |> List.map Equation
           |> equalitiesToPairs)

let internal transformNegativeEq =
    function
    | (Product ((Number _ as n)::_) as l, r) -> l / n, Algebraic.expand (r / n)
    | l,r -> l, Algebraic.expand r

let deriveShallowSums (eqs : Equation list) =
    eqs
    |> List.collect (fun eq ->
           let l, r = eq.Definition
           match r with
           | Sum sums ->
               (l, r)
               :: (sums |> List.map (fun x -> transformNegativeEq (x, l - (r - x))))
           | _ -> [l,r])
    |> List.map Equation
    |> equalitiesToPairs       

let deriveShallowEqualities eqs =
    let deqs = Hashset(deriveShallowSums eqs)
    deqs.UnionWith(deriveEqualitiesFromProduct eqs)
    Seq.toList deqs

let deriveEqualities eqs =
    let deqs = Hashset(deriveShallowEqualities eqs)
    deqs.UnionWith(deriveAndGenerateEqualities eqs)
    Seq.toList deqs