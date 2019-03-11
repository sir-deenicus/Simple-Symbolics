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
open Units

let getCandidates (vset : Hashset<_>) vars knowns =
    knowns
    |> Seq.filter
           (fun (v1, e) ->
           let v1isVar = Expression.isVariable v1
           v1isVar && not (vset.Contains v1)
           && vars |> Seq.exists (fun (v, _) -> e |> containsVar v))

let getSolutions evaluate vset vars candidates =
    [ for (e, e2) in getCandidates vset vars candidates do
          match evaluate vars e2 with
          | None -> ()
          | Some v -> yield e, v ]

let iterativeSolve eval vars knowns =
    let vset =
        vars
        |> Seq.map fst
        |> Hashset

    let rec loop cs tsols (vs : seq<_>) =
        let candidates = getCandidates vset vs knowns
        let sols = getSolutions eval vset vs candidates
        match sols with
        | [] -> List.concat tsols |> List.rev, cs
        | sols ->
            sols
            |> List.iter (fst
                          >> vset.Add
                          >> ignore)
            let vars' = sols @ List.ofSeq vs
            loop (List.ofSeq candidates :: cs) (sols :: tsols) vars'

    loop [] [] vars

let iterativeSolve2 f eval vars knowns =
    let vset =
        vars
        |> Seq.map fst
        |> Hashset

    let rec loop ts cs tsols (vs : seq<_>) =
        let candidates = getCandidates vset vs knowns
        let sols = getSolutions eval vset vs candidates
        match sols with
        | [] -> List.concat tsols |> List.rev, cs, ts
        | sols ->
            sols
            |> List.iter (fst
                          >> vset.Add
                          >> ignore)
            let vars' = sols @ List.ofSeq vs
            let vmap = Dict.ofSeq (Seq.map (keepLeft f) vars')
            let ts' =
                candidates |> Seq.map (fun (e, e2) -> e, replaceSymbols vmap e2)
            loop (List.ofSeq ts' :: ts) (List.ofSeq candidates :: cs)
                (sols :: tsols) vars'

    loop [] [] [] vars

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

let varsu =
    [ tc, 350 * K
      qc, 6300 * J
      th, 650 * K ]

let zx, zy = iterativeSolve Expression.evaluateFloat vars knowns
let zxu, zyu = iterativeSolve Units.tryEvaluateUnits varsu knowns

Units.evaluateUnits
zxu |> List.map (keepLeft Units.simplifyUnits)


open Core.Vars

let suntemp = symbol "T_\\odot"
let sunLum = symbol "L_\\odot"
let earthLum = symbol "L_\\oplus"
let sunrad = symbol "R_\\odot"
let earthtemp = symbol "T_\\oplus"
let earthrad = symbol "R_\\oplus"
let earthsundistpow = symbol "E_\\oplus"
let earthsundist = symbol "a_0"
let earthabs = symbol "E_absorb"
let sigma = symbol "\\sigma"
let lum c T r = 4 * pi * r ** 2 * T ** 4 * c

//= lum sigma earthtemp earthrad
let thermknown =
    deriveAndGenerateEqualities [ sunLum <=> lum sigma suntemp sunrad

                                  earthsundistpow
                                  <=> sunLum / (4 * pi * earthsundist ** 2)

                                  earthabs
                                  <=> pi * earthrad ** 2 * earthsundistpow
                                  earthLum <=> lum sigma earthtemp earthrad
                                  earthLum <=> earthabs ]

let zx, zy =
    iterativeSolve Units.tryEvaluateUnits [ suntemp, 5778 * K
                                            sunrad, 695_510 * km ] thermknown

