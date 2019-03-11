//HIDDENX
//#I @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45"
#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\Lab"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45\Prelude.dll"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45\Hansei.Core.dll"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45\Hansei.dll"
//#r "prelude.dll"
//#r "hansei.core.dll"
//#r "hansei.dll"
#load "solving.fsx"

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
open Prelude.Math

let exprIsLog =
    function
    | Function(Ln, _) -> true
    | _ -> false

let xIsMultipleOfy y x = x % y = 0

let isCertainlyMultiple tester f =
    let isMultiple =
        function
        | Number n -> n.IsInteger && tester (int n)
        | Product(Number p :: ps) -> p.IsInteger && tester (int p)
        | _ -> false
    match f with
    | f when isMultiple f -> true
    | Sum l -> List.forall isMultiple l
    | _ -> false

let collectIntegerTerms i x =
    let nums = Structure.collectNumbers x
    let l = nums.Length - 1
    if l < 0 then x
    else Polynomial.collectTerms nums.[min l i] x

let collectSymbolTerms i x =
    let ids = Structure.collectIdentifiers x
    let l = ids.Length - 1
    if l < 0 then x
    else Polynomial.collectTerms ids.[min l i] x

let filterProductWith f =
    function
    | Product l -> Some(List.filter f l)
    | _ -> None

let baseOfPower =
    function
    | Power(b, _) -> Some b
    | _ -> None

let number =
    function
    | Number n -> Some n
    | _ -> None

let splitPowerIn2ByN nInt =
    let n = Expression.FromInt32 nInt
    function
    | Power(b, (Sum(Number _ :: _) as r)) ->
        Core.Algebraic.simplifyLite (b ** n * Power(b, r - n))
    | f -> f

let splitPower =
    function
    | Power(b, (Sum l)) ->
        Core.Algebraic.simplifyLite (List.map (fun e -> b ** e) l |> Product)
    | f -> f

let reduceProductOne =
    function
    | Product((Number _ as n) :: l) ->
        Core.Algebraic.simplifyLite ((n - 1) * Product l + Product l)
    | f -> f

let reduceProduct cInt =
    let c = Expression.FromInt32 cInt
    function
    | Product((Number _ as n) :: l) ->
        Core.Algebraic.simplifyLite (Sum [ Product [ (n - c)
                                                     Product l ]
                                           (n - (n - c)) * Product l ])
    | f -> f

let rootExprLength =
    function
    | Sum l | Product l -> List.length l
    | _ -> -1

let isNegativePower =
    function
    | Power(e, Number n) -> n < 0N
    | _ -> false

let solveProductForm e =
    function
    | (Product l) as p ->
        l
        |> List.map (fun e2 ->
               let r = (p * (1 / e2)) / e
               if isNegativePower e2 then r, 1 / e2
               else 1Q / r, e2)
    | _ -> []

let applyAtIndex i findex f =
    function
    | Product l ->
        List.mapi (fun j e ->
            if i = j then f findex e
            else e) l
        |> Product
    | Sum l ->
        List.mapi (fun j e ->
            if i = j then f findex e
            else e) l
        |> Sum
    | e -> e

let indexableFunction e = e
let ignoreFirst f _ = f

let options =
    [ Algebraic.expand, "Expand"
      Rational.reduce, "Reduce fractions"
      Rational.rationalize, "rationalize terms"
      Rational.expand, "expand fractions"
      indexableFunction, "indexable function"
      Logarithm.expand, "apply logarithm product/quotient rule, expand"
      Logarithm.contract, "apply logarithm product/quotient rule, contract"
      Logarithm.powerRule, "apply logarithm power rule"
      Algebraic.simplify true, "simplify expression" ]

// let poptions =
//     List.zip ([| 1..options.Length |]
//               |> Array.map (konst 1.)
//               |> Array.normalize
//               |> Array.toList) options
let isCertainlyEven = isCertainlyMultiple (xIsMultipleOfy 2)
let isCertainlyOdd = isCertainlyEven >> not

let makeCertainlyEven x =
    if isCertainlyEven x then x
    else 2 * x

//let makeCertainlyOdd x = if isCertainlyEven x then 2*x + 1 else x
let makeCertainlyOdd x =
    if isCertainlyEven x then x + 1
    else 2 * x + 1

type FunctionInputType =
    | Parameter of (int -> Expression -> Expression)
    | NoParam of (Expression -> Expression)
    | Index of (int -> Expression -> Expression)

let indexableFunc =
    [ Parameter reduceProduct, "apply reduce product at "
      Parameter splitPowerIn2ByN, "move power left "
      Index collectIntegerTerms, "apply collect integers at "
      Index collectSymbolTerms, "apply collect vars at "
      NoParam reduceProductOne, "reduce product by one"
      //NoParam makeCertainlyEven, "write as even";
      NoParam splitPower, "split powers " ]

//NoParam makeCertainlyOdd, "write as odd"
let sampleFunction e =
    cont {
        let l = rootExprLength e
        let! (ft, d) = uniform indexableFunc
        let f, ps =
            match ft with
            | Parameter f -> f, uniform [ 1..60 ]
            | NoParam f -> ignoreFirst f, exactly -1
            | Index f -> f, uniform [ 0..70 ]
        let! j = ps
        if l = -1 then return (f j e, (d, j, -1))
        else let! i = uniform [ 0..l - 1 ]
             return (applyAtIndex i j f e, (d, i, j))
    }

let findPath options targetCond sourceexpr =
    let containsLog = Structure.existsRecursive exprIsLog sourceexpr
    let options' = //remove operations that are un-needed
        List.filter
            (fun (_, str : string) ->
            not (str.Contains "logarithm") || containsLog) options

    let rec loop path currentexpr =
        cont {
            let! chosenOp, desc = uniform options'
            let! expr', (desc', i, j) = match desc with
                                        | "indexable function" ->
                                            sampleFunction currentexpr
                                        | _ ->
                                            exactly
                                                (chosenOp currentexpr,
                                                 (desc, -1, -1))
            //do! constrain (List.isEmpty path || fst3 (List.head path) <> desc')
            if targetCond expr' then return List.rev ((desc', i, j) :: path)
            else
                // do! constrain ((currentexpr <> expr'))
                return! loop ((desc', i, j) :: path) expr'
        }
    loop [] sourceexpr

let findpath targetCond sourceexpr = findPath options targetCond sourceexpr
let searcher = Model(findpath isCertainlyEven (x + y))
let funcLookUp = Map(List.map swap options)
let funcLookUpApp = Map(List.map swap indexableFunc)

let run x =
    match Map.tryFind x funcLookUp with
    | None ->
        match Map.tryFind x funcLookUpApp with
        | None -> failwith "impossible"
        | Some(x) -> ()
    | _ -> ()

let prooftest e =
    match Structure.removeExpression (2Q ** (3 * k + 1) + 5) e with
    | None -> false
    | Some e' -> isCertainlyMultiple (xIsMultipleOfy 7) e'

let searcher2 = Model(findpath prooftest (2Q ** (3 * k + 4) + 5))

searcher2.Reify()
searcher2.ImportanceSample(nsamples = 55000, maxdepth = 58)
|> Hansei.Utils.normalize
|> List.sortByDescending fst
Model(findpath ((=) (ln (x ** (s - 1)) + (-r * x))) (ln (x ** (s - 1Q) * exp (-r * x))))
    .ImportanceSample(2000, 18)

let eq = 8 * 2Q ** (3 * n + 1) + 5
let zq = eq |> applyAtIndex 1 -1 (ignoreFirst reduceProductOne)
let zq' = Structure.removeExpression ((2Q ** (3 * n + 1) + 5)) zq

isCertainlyMultiple (xIsMultipleOfy 7) zq'.Value
replaceExpression z (d ** (a + b + c)) (e * d ** (a + b + c)) = e * z
replaceExpression z (d ** (a + b + c)) (d ** (a + b + c)) = z
replaceExpression z (a + b + c) (a + b + c) = z
replaceExpression z (a + b) (a + b + c) = z + c
replaceExpression z (a * b) (a * b + (c + 2Q ** (a * b))) = (z + (c + 2Q ** z))
replaceExpression z a (a * b + (c + 2Q ** (a * b))) = (z * b
                                                       + (c + 2Q ** (z * b)))
replaceSymbol z a (a * b + (c + 2Q ** (a * b)))
|> Algebraic.simplify true = (z * b + (c + 2Q ** (z * b)))
containsExpression ((2Q ** (3 * n + 1) + 5)) zq
Structure.removeExpression ((2Q ** (3 * n + 1) + 5)) zq

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
      meter, "length", UnitsDesc.length ]

[ for (a, _, _) in usefulUnits do
      for (b, _, _) in usefulUnits do
          for (c, _, _) in usefulUnits ->
              ((a * b) * c).Unit = (a * (b * c)).Unit ]
|> List.forall id
[ for (a, _, _) in usefulUnits -> (a * unitless).Unit = a.Unit ]
|> List.forall id
[ for (a, _, _) in usefulUnits -> (a * 1 / a).Unit = unitless.Unit ]
|> List.forall id

let rec unitsPath wasrecip path (curA : Expression) (cur : Units)
        (target : Units) =
    cont {
        let! op = uniform [ Times; Reciprocal; Divide ]
        do! constrain (not (wasrecip && op = Reciprocal))
        let! units, desc0, acts = uniform usefulUnits
        let next, desc, un, curA' =
            match op with
            | Times -> cur * units, units.AltUnit, desc0, curA * acts
            | Divide -> cur / units, units.AltUnit, desc0, curA / acts
            | Reciprocal -> 1Q / cur, "", "", 1Q / curA

        let perf = (op, un, desc)
        if next.Unit = target.Unit then
            return (curA'.ToFormattedString(), List.rev (perf :: path))
        else
            return! unitsPath (op = Reciprocal) (perf :: path) curA' next target
    }

Model(unitsPath false [] 1Q Units.stefan_boltzman unitless)
    .ImportanceSample(2500, 50)
|> List.sortByDescending fst
|> Seq.takeOrMax 5
Model(unitsPath false [] 1Q unitless W)
    .ImportanceSample(2500, 50)
|> List.sortByDescending fst
|> Seq.takeOrMax 15
|> Seq.toArray
Model(unitsPath false [] 1Q J (sec)).ImportanceSample(500, 50)
|> List.sortByDescending fst
|> Seq.takeOrMax 5
(meter / sec) * N / W

///////////////
///
///
///
let containsEmpty S = Set.contains Set.empty S

let closedUnderIntersection (S : Set<Set<_>>) =
    Array.fold (&&) true [| for A in S do
                                for B in S -> S.Contains(Set.intersect A B) |]

let powerset (els : 'a seq) =
    let asArray = Seq.toArray els
    let n = float asArray.Length
    let l = int n
    seq {
        for i in 0.0..2. ** n - 1. ->
            let pattern = baseNumToArray l (toBase 2. i)
            [| for i in 0..l - 1 do
                   if pattern.[i] = 1. then yield asArray.[i] |]
    }

let unionCountable S =
    let asArray = Set.toArray S
    let n = float asArray.Length
    let l = int n
    [ for i in 0.0..2. ** n - 1. ->
          let pattern = baseNumToArray l (toBase 2. i)

          let sets =
              [| for j in 0..l - 1 do
                     if pattern.[j] = 1. then yield asArray.[j] |]
          Array.contains (Set.unionMany sets) asArray ]
    |> List.fold (&&) true

let topologyFilter pset =
    let empt = containsEmpty pset
    let union = unionCountable pset
    let inter = closedUnderIntersection pset
    empt && union && inter

let rec createtop n tops curtop (pset : 'a [] list) =
    cont {
        if n = 0 then return Set.add curtop tops
        else
            let! set = uniform pset
            let top' = Set.add (Set set) curtop
            do! constrain (topologyFilter top')
            let tops' = Set.add top' tops
            do! constrain (tops' <> tops)
            return! createtop (n - 1) tops' top' pset
    }

let pset = powerset [ "dog"; "cat"; "moose"; "penguin" ] |> Seq.toList

topologyFilter (List.map Set.ofArray pset |> Set.ofList)
topologyFilter (set [ Set.empty ])

let top = Model(createtop 3 (Set.empty) (set [ Set.empty ]) pset)
              .ImportanceSample(2, 50) |> List.sortByDescending fst

/////////////////////
///
let findPathUsingEqualities terminationCondition equalities (seen : Hashset<_>)
    startExpression targetExpression =
    let rec search path currentExpression =
        cont {
            if terminationCondition targetExpression currentExpression then
                return path
            else
                let applicable =
                    List.filter
                        (fun (a, b) -> containsExpression a currentExpression)
                        equalities
                match applicable with
                | [] -> return! fail()
                | _ ->
                    let! e1, e2 = uniform applicable
                    let expressionNew =
                        replaceExpression e2 e1 currentExpression
                    do! constrain
                            (not
                                 (seen.Contains
                                      (Rational.rationalize expressionNew)))
                    let msg =
                        sprintf
                            @"%s = %s \; \left( \textrm{because} \; %s = %s\right)"
                            (currentExpression.ToFormattedString())
                            (expressionNew.ToFormattedString())
                            (e1.ToFormattedString()) (e2.ToFormattedString())
                    seen.Add expressionNew |> ignore
                    return! search (msg :: path) expressionNew
        }
    search [] startExpression

let rewriteExpectationAsIntegral = function
    | FunctionN(Function.Expectation, [ expr; distr ]) ->
        let dx =
            match Structure.first Expression.isVariable expr with
            | Some e -> [ e ] | None -> []
        FunctionN(Function.Integral, (distr * expr) :: dx)
    | f -> f    

let rewriteIntegralAsExpectation = function
    | FunctionN(Function.Integral, Product l :: _) ->
        maybe {
            let! p = List.tryFind (function
                         | FunctionN(Probability, _) -> true
                         | _ -> false) l
            return FunctionN(Function.Expectation,
                             [ (Product l) / p; p ]) }
    | _ -> None

let bringGradientOutIntegral =
    function
    | FunctionN(Function.Integral, Function(Gradient, expr) :: rest) ->
        Function(Gradient, FunctionN(Function.Integral, expr :: rest))
    | f -> f

let bringIntegralOutGradient =
    function
    | Function(Gradient, FunctionN(Function.Integral, expr :: rest)) ->
       FunctionN(Function.Integral, Function(Gradient, expr) :: rest)  
    | f -> f

Function(Gradient, FunctionN(Integral,[x;x])) |> Expression.toFormattedString


Function(Gradient, FunctionN(Integral,[x;x])) |> Expression.toFormattedString

FunctionN(Integral,[FunctionN(Integral,[x;x]);y]) |> Expression.toFormattedString

FunctionN(Function.Expectation, [ x; z ])  |> Expression.toFormattedString

FunctionN(Function.Integral, [ x**2;x]) |> rewriteIntegralAsExpectation

grad (integral x x)
let ez = integral x (prob x * grad x)
Structure.collectDistinctWith (function | Identifier _ | Function _ | FunctionN(Probability,_) -> true  | _ -> false) ez

Structure.recursiveMap (function FunctionN(Probability,_) -> 1Q | f -> f  ) ez