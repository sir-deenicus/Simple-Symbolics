#I @"C:\Users\Admin\Documents\Visual Studio 2017\Projects\Hansei\Hansei\bin\Release\net45"
#r "prelude.dll"
#r "hansei.core.dll"
#r "hansei.dll"
#load "solving.fsx"

open System.Collections.Generic
open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics
open MathNet.Symbolics
open Solving
open Hansei
open Hansei.Core
open Hansei.Continuation
open Hansei.Core.Distributions
open System
open Prelude.Common 
open Prelude.StringMetrics

let pchoice = [0.3;0.2;0.15;0.15;0.05;0.05;0.05;0.05]

let options =
    [Algebraic.expand,"Expand"
     Rational.reduce,"Reduce fractions"
     Rational.rationalize,"rationalize terms"
     Rational.expand,"expand fractions"
     Logarithm.expand,"logarithm product or quotient rule, expand"
     Logarithm.contract,"logarithm product or quotient rule, contract"
     Logarithm.powerRule,"logarithm power rule"
     Algebraic.simplify true,"simplify expression"]

let poptions = List.zip pchoice options

let exprContainsLog =
    function 
    | Function(Ln,_) -> true
    | _ -> false

let transformExpr targetexpr sourceexpr =
    let targetstr = Expression.toPlainString targetexpr
    let containsLog = Structure.filterRecursive exprContainsLog sourceexpr
    let options' = //remove operations that are un-needed
        List.filter 
            (fun (_,str: string) -> not(str.Contains "logarithm") || containsLog) 
            options
    
    let rec loop path currentexpr =
        cont {
            let! chosenOp,desc = uniform options'
            let expr' = chosenOp currentexpr
            if expr' = targetexpr then return List.rev (desc::path)
            else 
                do! constrain(currentexpr <> expr')
                let str' = Expression.toPlainString expr'
                let reward = stringSimilarityDice targetstr str' //bias search towards string that are more like our target
                let! p = uniform_float 20
                do! constrain(reward > p)
                return! loop (desc::path) expr'
        }
    loop [] sourceexpr

let sigma2,sigma1 = Operators.symbol "\sigma_2",Operators.symbol "\sigma_1"
let sc =
    (1 / 2Q * ln(2 * pi * sigma2 ** 2) 
     + -1 / 2Q * (1 + ln(2 * pi * sigma1 ** 2)))
let tc =
    (1 / 2Q * ln(2 * pi * sigma2 ** 2) 
     + -1 / 2Q * (1 + ln(2 * pi * sigma1 ** 2))) |> Logarithm.powerRule //|> Rational.expand  |> Logarithm.contract |> Algebraic.simplify true 
let searcher = Model(transformExpr tc sc)

exprContainsLog tc

searcher.ImportanceSample(100,20)
///////////////////////////
/// ////////////////////

let rec findVariablesOfExpression = function 
   | Identifier _ as var -> [var]
   | Power(x, n) -> findVariablesOfExpression x @ findVariablesOfExpression n
   | Product l 
   | Sum     l -> List.collect findVariablesOfExpression l
   | Function (_, x) -> findVariablesOfExpression x   
   | _ -> []

let deriveTrivialEqualitiesSingle (e1,eq) = 
    [ yield Equation(e1,eq)
      for var in findVariablesOfExpression eq do 
       match reArrangeEquation0 true var (eq, e1) with
       | Identifier _ as var, req -> yield Equation(var, req) 
       | _ -> () ]

let deriveTrivialEqualities (eqs: Equation list) =
    let deqs =
      [for eq in eqs do 
        yield! deriveTrivialEqualitiesSingle eq.Equalities.Head ]
    Hashset deqs |> Seq.toList

let genEqualitiesList (eqs:Equation list) = [for e in eqs do yield! e.Equalities]

let equals a b = Equation(a,b)

let ``P(A|B)`` = symbol "P(A|B)"
let ``P(A ∩ B)`` = Operators.symbol "P(A ∩ B)"
let ``P(B)`` = Operators.symbol "P(B)"
let ``P(A)`` = Operators.symbol "P(A)"
let ``P(B|A)`` = Operators.symbol "P(B|A)"

let tryFindCompoundExpression (expressionToFindContentSet: Hashset<_>) (expressionList:_ list) =
    let expressionListSet = Hashset expressionList
    expressionToFindContentSet.IsSubsetOf expressionListSet 

let containsExpression expressionToFind formula = 
   let expressionToFindContentSet = Hashset(expressionToList expressionToFind)    
   let rec iterFindIn = function
   | Identifier _ as var when var = expressionToFind -> true
   | Power(p, n) -> iterFindIn p || iterFindIn n    
   | Function(_, fx)  ->  iterFindIn fx
   | Product l ->  tryFindCompoundExpression expressionToFindContentSet l || (List.exists iterFindIn l)
   | Sum     l ->  tryFindCompoundExpression expressionToFindContentSet l || (List.exists iterFindIn l)
   | _ -> false
   iterFindIn formula  

let feq equalities (seen : Hashset<_>) eq0 eq1 = 
    let rec search path ec = cont {  
       if containsExpression eq1 ec then return path
       else  
        let! e1,e2 = uniform equalities 
        do! constrain (containsExpression e1 ec) 
        let ec' = replaceExpression e2 e1 ec
        do! constrain (not (seen.Contains (Rational.rationalize ec')))
        let msg = sprintf "replace %s with %s in %s" (e1.ToFormattedString()) (e2.ToFormattedString()) (ec.ToFormattedString())
        //printfn "%s" msg
        printfn "Old: %s => New: %s" (ec.ToFormattedString()) (ec'.ToFormattedString())
        seen.Add ec' |> ignore
        return! search (msg::path) ec'  }
    search [] eq0

let feq2 equalities (seen : Hashset<_>) eq0 eq1 = 
    let rec search path ec = cont {  
       seen.Add eq0 |> ignore
       if eq1 = ec then return path
       else  
         let! replace = bernoulli 0.5
         if replace then 
            let! e1,e2 = uniform equalities
            do! constrain (containsExpression e1 ec) 
            let ec' = replaceExpression e2 e1 ec
            do! constrain (not (seen.Contains (Rational.rationalize ec')))
            let msg = sprintf "%s = %s" (ec.ToFormattedString()) (ec'.ToFormattedString())
            //printfn "%s" msg
            //printfn "Old: %s => New: %s" (ec.ToFormattedString()) (ec'.ToFormattedString())
            seen.Add ec' |> ignore
            return! search (msg::path) ec'
         else let variables = findVariablesOfExpression ec
              let! desc, op = uniform ( (List.map (fun (x:Expression) -> ("*" + (x.ToFormattedString())), (*) x) variables) @
                                        (List.map (fun (x:Expression) -> ("/" + (x.ToFormattedString())), flip (/) x) variables))
              //printfn "%s" desc
              let ec' = op ec
              do! constrain (not (seen.Contains (Rational.rationalize ec')))
              let s = ec.ToFormattedString()
              let s' = ec'.ToFormattedString()
              let msg = s + desc + " = " + s'
              return! search (msg::path) ec' }
    search [] eq0

let equalities =
    deriveTrivialEqualities [``P(A|B)`` </equals/> (``P(A ∩ B)``/``P(B)`` )
                             ``P(B|A)`` </equals/> (``P(A ∩ B)``/``P(A)`` ) ]      

let eqls = genEqualitiesList equalities
eqls
let model seen = Model(feq eqls seen ``P(A|B)`` ``P(B|A)``) 
let extractValue = function | Value x -> x | _ -> failwith "error"
(model (Hashset())).ImportanceSample(5,2) |> Utils.normalize |> List.map (fun (p, l) -> string p + ", " + (List.rev (extractValue l) |> String.concat "\n"  )) |> String.concat "\\"
 

let model2 seen = Model(feq2 eqls seen ``P(A|B)`` ``P(B|A)``) 

(model2 (Hashset())).ImportanceSample(15000,15) |> List.rev |> Utils.normalize 

ln (exp 2Q) |> Algebraic.simplify true

exp 2Q

log 1.

