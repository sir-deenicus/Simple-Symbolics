#r "netstandard"
#I @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Debug\net47" 
#r "hansei.core.dll"
#r "hansei.dll"
#r @"C:\Users\cybernetic\Code\Libs\net4+\Fsharp.data\FSharp.Data.dll"
#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\bin\Debug\net47"
#r @"C:\Users\cybernetic\source\repos\Prelude\Prelude\bin\Release\net47\prelude.dll"
#r @"C:\Users\cybernetic\source\repos\EvolutionaryBayes\EvolutionaryBayes\bin\Debug\net47\EvolutionaryBayes.dll"
#r @"MathNet.Numerics.dll" 
#r @"MathNet.Numerics.Fsharp.dll"
#r @"MathNet.Symbolic.Ext.dll"
#r @"Simple-Symbolics.dll"
#r @"C:\Users\cybernetic\Documents\Papers\LiterateUtils\LiterateUtils\bin\Release\net47\LiterateUtils.dll"

#time "on"
//#load "..\disputil.fsx"

open Prelude.Math
open System
open System.IO
open MathNet.Symbolics
open Core
open Core.Vars
open Integration
open Hansei
open Hansei.Continuation
open Hansei.Core
open Hansei.Core.Distributions
open MathNet.Numerics
open Prelude.Common
open EvolutionaryBayes.RegretMinimization
open LiterateUtils.Types
open LiterateUtils
open MathNet.Symbolics.Differentiation 
open Utils 
open Searcher
//open Disputil
open MathNet.Symbolics.Core
open Prelude.Common

//Utils.useDir <- @"C:\Users\cybernetic\Jupyter-Notebooks\"

open Units 

type Unitsop =
    | Reciprocal
    | Times
    | Divide 
     

let usefulUnits =
    [ W, "Power", UnitsDesc.power
      J, "Energy", UnitsDesc.energy
      N, "Force", UnitsDesc.force
      K, "Temperature", UnitsDesc.temperature
      W / meter ** 2, "Energy flux", UnitsDesc.energyflux
      meter ** 3, "volume", UnitsDesc.volume
      meter / sec, "velocity", UnitsDesc.velocity
      meter / sec ** 2, "Acceleration", UnitsDesc.accel
      sec, "Time", UnitsDesc.time
      kg, "mass", UnitsDesc.mass
      meter, "length", UnitsDesc.length 
      kg / liter, "Density", UnitsDesc.density ]

let rec unitsPath wasrecip path (curA : Expression) (cur : Units)
        (target : Units) =
    cont {
        let! op = uniform [ Times; Reciprocal; Divide ]
        do! constrain (not (wasrecip && op = Reciprocal))
        let! units, desc0, unitsDesc = uniform usefulUnits
        let next, desc, opname, curA' =
            match op with
            | Times -> cur * units, units.AltUnit, desc0, curA * unitsDesc
            | Divide -> cur / units, units.AltUnit, desc0, curA / unitsDesc
            | Reciprocal -> 1Q / cur, "", "", 1Q / curA

        let perf = (op, opname, desc)
        if next.Unit = target.Unit then
            return (curA'.ToFormattedString(), List.rev (perf :: path))
        else
            return! unitsPath (op = Reciprocal) (perf :: path) curA' next target
    }

Model.ImportanceSample(unitsPath false [] UnitsDesc.energyflux (W / meter ** 2)  Units.stefan_boltzman, 2000, 100)
|> List.sortByDescending fst
|> Seq.takeOrMax 5


Model.ImportanceSample(unitsPath false [] UnitsDesc.energy J W, 200, 190)
|> ProbabilitySpace.mapValues fst
|> List.sortByDescending fst
|> Seq.takeOrMax 15 
|> Seq.toArray

Model.ImportanceSample(unitsPath false [] UnitsDesc.volume (meter **3) kg, 200, 20)
|> List.sortByDescending fst
|> Seq.takeOrMax 10
|> Seq.toArray
//
Model.ImportanceSample(unitsPath false [] 1Q unitless Units.stefan_boltzman, 1200, 100)
|> List.sortByDescending fst
|> Seq.takeOrMax 10
|> Seq.toArray



let aa0 =
    unitsPath false [] 1Q unitless Units.stefan_boltzman//  UnitsDesc.energy J W// UnitsDesc.energy J W
    //unitsPath false [] UnitsDesc.volume (meter **3) kg
    |> best_first_sample_dist None None 32. 100 16 40 4500
    //|> fun v -> v.Values
    //|> List.sortBy fst
aa0.Paths |> keyValueSeqtoPairArray
unitsPath false [] UnitsDesc.energyflux (W / meter ** 2) Units.stefan_boltzman//  UnitsDesc.energy J W// UnitsDesc.energy J W
      
unitsPath false [] UnitsDesc.volume liter kg 
