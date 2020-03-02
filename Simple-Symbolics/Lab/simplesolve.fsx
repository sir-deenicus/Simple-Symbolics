//HIDDENX
//#I @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net45"
#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\Lab"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net47\Prelude.dll"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net47\Hansei.Core.dll"
#r @"C:\Users\cybernetic\source\repos\Hansei\Hansei\bin\Release\net47\Hansei.dll"
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
open Prelude.Math
open Core.Vars
open Core
open MathNet.Numerics
open Prelude.Common
open System
open Hansei.Core.Distributions
open Prelude.StringMetrics
open Derivations
open Units
open Solving


let getCandidates1 (vset : Hashset<_>) vars knowns =
    knowns
    |> Seq.filter
           (fun (v1, e) ->
           let v1isVar = Expression.isVariable v1
           v1isVar && not (vset.Contains v1)
           && vars |> Seq.exists (fun (v, _) -> e |> containsVar v))

let getCandidates filter vars knowns =
    knowns
    |> Seq.filter
           (fun (v1, e) ->
           let v1isVar = Expression.isVariable v1
           v1isVar && filter v1
           && vars |> Seq.exists (fun (v, _) -> e |> containsVar v))  

let getSolutions evaluate filter vars candidates =
    [ for (e, e2) in getCandidates filter vars candidates do
          match evaluate vars e2 with
          | None -> ()
          | Some v -> yield e, v ]
 
let iterativeSolveGen filter eval vars knowns =
    let vset =
        vars
        |> Seq.map fst
        |> Hashset

    let rec loop n prevcount exit cs tsols (vs : seq<_>) =
        let candidates = getCandidates (filter vset) vs knowns
        let sols = getSolutions eval (filter vset) vs candidates
        match sols, n = 3 with
        | _, true
        | [], _ -> List.concat tsols |> List.rev, cs
        | sols, false ->
            let vcount = List.concat tsols |> List.map snd |> Hashset
            sols
            |> List.iter (fst
                          >> vset.Add
                          >> ignore)
            let vars' = sols @ List.ofSeq vs
            loop (n+1) vcount.Count (vcount.Count = prevcount) (List.ofSeq candidates :: cs) (sols :: tsols) vars'

    loop 0 0 false [] [] vars
    //not (vset.Contains v1)

let iterativeSolve eval vars knowns = 
    iterativeSolveGen (fun h v -> not (h.Contains v)) eval vars knowns


let redovar vars =
    let equals = 
        vars |> Seq.filter (fun (eq:Equation) ->
            let e1,e2 = eq.Definition
            Expression.isVariable e1 && Expression.isVariable e2 && e1 <> e2)
    [ for eq in equals do
        let a,b = eq.Definition
        for eq2 in vars do 
            let e1, e2 = eq2.Definition
            if e1 <> a && e2 <> a && (containsVar a e2 || containsVar a e1) then
                yield replaceSymbol b a e1 <=> replaceSymbol b a e2 ]
 
let vars = [ a ** 2 + b ** 2 <=> c ** 2;a <=> b ] 
redovar vars
let iterativeSolveb eval vars knowns = iterativeSolveGen (fun _ _ -> true) eval vars knowns
 
//let getCandidatesb vars knowns =
//    knowns
//    |> Seq.filter
//           (fun (v1, e) ->
//           let v1isVar = Expression.isVariable v1
//           v1isVar
//           && vars |> Seq.exists (fun (v, _) -> e |> containsVar v))

//let getSolutionsb evaluate vars candidates =
//    [ for (e, e2) in getCandidatesb vars candidates do
//          match evaluate vars e2 with
//          | None -> ()
//          | Some v -> yield e, v ]

//let iterativeSolveb eval vars knowns = 

//    let rec loop n cs tsols (vs : seq<_>) =
//        let candidates = getCandidatesb vs knowns
//        let sols = getSolutionsb eval vs candidates
//        match sols with
//        | _ when n = 3 -> List.concat tsols |> List.rev, cs
//        | [] -> List.concat tsols |> List.rev, cs
//        | sols -> 
//            let vars' = sols @ List.ofSeq vs
//            loop (n+1) (List.ofSeq candidates :: cs) (sols :: tsols) vars'

 //  loop 0 [] [] vars
let knowns =
    deriveAndGenerateEqualities
        [ a ** 2 + b ** 2 <=> c ** 2 
          a <=> b]
let knowns2 =
    deriveAndGenerateEqualities
        [ a ** 2 + b ** 2 <=> c ** 2  ] 
let evalExpr vars x =
    replaceSymbols (dict vars) x |> Expression.fullSimplify |> Some  

let evalExprNum vars x =
    let nums = vars |> Seq.filter (snd >> containsAnyVar >> not) 
    if Seq.isEmpty nums then None
    else let symb = replaceSymbols (dict nums) x |> Expression.fullSimplify
         if containsAnyVar symb then None else Some symb 

let eval = evalExpr    
    
let vars = [a, sqrt 2Q] 
(iterativeSolveb  evalExpr  [c, 4Q]   knowns2 |> fst |> List.map (pairapply Infix.format) )  
(iterativeSolveb evalExpr [a, sqrt 2Q]   knowns2 |> fst |> List.map (pairapply Infix.format) )  

(iterativeSolve Expression.evaluateFloat [a, sqrt 2.] knowns2 |> fst )  

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

[ a ** 2 + b ** 2 <=> c ** 2
  a ** 2 <=> b **2 ]
let knowns =
    deriveAndGenerateEqualities 
        [   eff <=> 1 - tc / th
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
 
zxu |> List.map (keepLeft Units.simplifyUnits)
 
let suntemp = symbol "T_\\odot"
let sunLum = symbol "L_\\odot"
let earthLum = symbol "L_\\oplus"
let earthLumAlb = symbol "L_\\oplus^a"
let sunrad = symbol "R_\\odot"
let earthtemp = symbol "T_\\oplus"
let earthrad = symbol "R_\\oplus"
let earthsundistpow = symbol "E_\\oplus"
let earthsundist = symbol "a_0"
let earthabs = symbol "E_absorb"
let sigma = symbol "\\sigma"

let lum c T r = 4 * pi * r ** 2 * T ** 4 * c

let thermknown =
    deriveAndGenerateEqualities [ sunLum <=> lum sigma suntemp sunrad
                                  earthsundistpow <=> sunLum / (4 * pi * earthsundist ** 2) 
                                  earthabs <=> pi * earthrad ** 2 * earthsundistpow
                                  earthLum <=> lum sigma earthtemp earthrad
                                  earthLum <=> earthabs 
                                  earthLumAlb <=> earthLum * 7/10Q ]

 
iterativeSolve Units.tryEvaluateUnits [ suntemp, 5778 * K
                                        sunrad, 695_510 * km ] thermknown

#r @"C:\Users\cybernetic\source\repos\EvolutionaryBayes\EvolutionaryBayes\bin\Debug\net46\EvolutionaryBayes.dll"
#r @"C:\Users\cybernetic\Code\Libs\MathNet\lib\net40\MathNet.Numerics.dll"
#time
open EvolutionaryBayes
open EvolutionaryBayes.ProbMonad
open EvolutionaryBayes.ParticleFilters
open Helpers

let mutate equalities l =
    let (_, currentExpression) = List.head l
    let applicable =
        List.filter (fun (a, b) -> containsExpression a currentExpression)
            equalities
    match applicable with
    | [] -> l
    | _ ->
        let e1, e2 =
            (applicable
             |> List.toArray
             |> Array.sampleOne)

        let expressionNew = replaceExpression e2 e1 currentExpression
        if currentExpression = expressionNew then l
        else
        (currentExpression, expressionNew)::l



//seen.Add expressionNew |> ignore
let pr = dist { let! e = Distributions.uniform (List.toArray thermknown)
                return [e] }
let scorer l = 
    let (_, e) = List.head l
    Structure.collectDistinctWith Expression.isCompact e
    |> List.length
    |> float

let zt =
    pr |> sequenceSamples 0.2 (mutate thermknown) scorer 100 10



let ``P(A|B)`` = symbol "P(A|B)"
let ``P(A ∩ B)`` = symbol "P(A ∩ B)"
let ``P(B)`` = symbol "P(B)"
let ``P(A)`` = symbol "P(A)"
let ``P(B|A)`` = symbol "P(B|A)"

let strrep (s:string) = s.Replace("A", "H").Replace("B", "X")  

let equalities =
    deriveTrivialEqualities [``P(A|B)`` <=> (``P(A ∩ B)`` / ``P(B)``)
                             ``P(B|A)`` <=> (``P(A ∩ B)`` / ``P(A)``)]
    |> List.map (Equation.map (replaceVariableSymbol strrep))   

let eqs = genEqualitiesList equalities   

let p_h = Operators.symbol "P(H)"
let p_hx = Operators.symbol "P(H|X)"
let p_c = Operators.symbol "P(C)"
let p_x = Operators.symbol "P(X)"
let p_xh = Operators.symbol "P(X|H)"

let eq0 = p_h * (1 + p_c * (p_xh/p_x - 1Q))

let pr2 =  (always [p_hx, eq0])

let targ = p_h * p_xh/p_x
let targstr = targ |> Infix.format

let scorer2 l = 
    let (_, e) = List.head l
    let len = float (List.length l)
    0.05/len + 1./(averageDepth e )



(a + b * a + (c*a))

let scorer2b l = 
    let (_, e) = List.head l
    let w = float (width e)
    let str = Infix.format e
    let sim = Prelude.StringMetrics.stringSimilarityDice str targstr
    1./w + 1./(averageDepth e ) + sim

let scorer3 l =
    let (_, e) = List.head l
    let str = Infix.format e
    Prelude.StringMetrics.stringSimilarityDice str targstr

let scorer3b l = 
    let (_, e) = List.head l
    let w = float (width e)
    let str = Infix.format e
    let sim = Prelude.StringMetrics.stringSimilarityDice str targstr
    1./w + 1./(averageDepth e ) + sim
let scorer3c l = 
    let (_, e) = List.head l
    let w = float (width e)
    let str = Infix.format e
    let sim = Prelude.StringMetrics.stringSimilarityDice str targstr
    1./w + sim  

let options2 =
    [|Algebraic.expand, "Expand"
      Rational.reduce, "Reduce fractions"
      Rational.rationalize, "rationalize terms"
      Rational.expand, "expand fractions"  
      Algebraic.simplify true, "simplify expression" |]

let mutate2 eqs l = 
    if random.NextDouble() < 0.333 then mutate eqs l
    elif random.NextDouble () < 0.333 * 2. then
        let (_, currentExpression) = List.head l
        let vars = Structure.collectAllPredicate Expression.isVariable currentExpression
        let e = Array.sampleOne (List.toArray vars)
        let nextexpr = Polynomial.collectTerms e currentExpression
   
        if nextexpr = currentExpression || nextexpr = Undefined then l
        else (currentExpression, nextexpr)::l
    else 
        let (_, currentExpression) = List.head l
        let f, _ = Array.sampleOne options2
        let nextexpr = f currentExpression
        if nextexpr = currentExpression then l
        else (currentExpression, nextexpr)::l

let scorer4 l = 
    let (_, e) = List.head l 
    if Expression.isSum e then 
        let w = float (Structure.rootWidth e)
        let str = Infix.format e
        let sim = Prelude.StringMetrics.stringSimilarityDice str targstr
        1./w + sim
    else 1e-6

let zt2 =
    pr2 |> sequenceSamples 0.4 (mutate2 eqs) scorer4 100 100
 

let ezl = zt2.Sample() |> List.map Equation |> List.rev
let ezz = zt2.SampleN(200) |> Array.maxBy (scorer4) |> List.map Equation |> List.rev
pr2.Sample() |> List.map Equation
 

zt |> importanceSamples scorer 20 |> Array.map snd
let choices = importanceSamples (scorer2) 100 pr2
let dist' = Distributions.categorical2 choices, Array.averageBy snd choices

let ztp = evolveSequence 0.4 100 [] (fun _ e -> mutate2 eqs e) scorer4 150 500 pr2 |> List.toArray |> Distributions.categorical2
let qz = ztp.Sample().Sample() |> List.map Equation |> List.rev

let ztp2, avp = evolveSequence 0.4 100 [] (fun _ e -> mutate2 eqs e) scorer4 100 500 pr2 |> List.maxBy snd 
let qz2 = ztp2.SampleN(200) |> Array.maxBy (scorer4) |> List.map Equation |> List.rev
let zzz =  ztp2.Sample() |> List.map Equation |> List.rev


///////////

let rewriteExpectationAsIntegral = function
    | FunctionN(Function.Expectation, [ expr; distr ]) ->
        let dx =
            match Structure.first Expression.isVariable expr with
            | Some e -> [ e ] | None -> []
        FunctionN(Function.Integral, (distr * expr) :: dx)
    | f -> f    

let rewriteIntegralAsExpectation = function
    | FunctionN(Function.Integral, Product l :: _) as f ->
        maybe {
            let! p = List.tryFind (function
                         | FunctionN(Probability, _) -> true
                         | _ -> false) l
            return FunctionN(Function.Expectation,
                             [ (Product l) / p; p ]) } |> Option.getDef f
    | f -> f
    
let bringGradientOutIntegral =
    function
    | FunctionN(Function.Integral, FunctionN(Gradient, expr::var) :: dx) ->
        FunctionN(Gradient, FunctionN(Function.Integral, expr :: dx)::var)
    | f -> f

let bringIntegralOutGradient =
    function
    | FunctionN(Gradient, FunctionN(Function.Integral, expr :: dx)::param) ->
       FunctionN(Function.Integral, FunctionN(Gradient, expr::param) :: dx)  
    | f -> f


let options3 =
    Array.append
        options2
        [|rewriteExpectationAsIntegral , "rewrite expectation as integral"
          rewriteIntegralAsExpectation , "rewrite integral as expectation"
          bringGradientOutIntegral, "bring gradient out integral"
          bringIntegralOutGradient, "bring integral out gradient"|]

let mutate3 eqs l = 
    if random.NextDouble() < 0.5 then mutate eqs l 
    else 
        let (_, currentExpression) = List.head l
        let f, s = Array.sampleOne options3
        let nextexpr = f currentExpression
        let q  = s
        if nextexpr = currentExpression then l
        else 
            (currentExpression, nextexpr)::l

let e1 = grad (ln(prob x))  
let e2 = grad (prob x)/prob x

let f_z = symbol "f(z)"
f_z.ToFormattedString()
let e3 = grad (expectation (prob x) f_z)

let eqs3 = deriveEqualitiesFromProduct [(e3,e3); e1,e2] 
eqs3 |> List.map (Equation >> string)

let eb = expectation (prob x) e1
eb.ToFormattedString()
let pr3 = Distributions.uniform [|[(x2,e3)]; [x,eb]|]
let scorerz l = 
    let (_, e) = List.head l
    let w = float (width e)
    w + 1./(averageDepth e )


let zt3 =
    pr3 |> sequenceSamples 0.4 (mutate3 eqs3) scorerz 100 100
   
let ezl2 = zt3.SampleN(200) |> Array.maxBy (scorerz) |> List.map Equation |> List.rev


let ezl2 = zt3.Sample() |> List.map Equation |> List.rev

/////////

let mutate equalities l =
    let (_, currentExpression,_) = List.head l
    let applicable =
        List.filter (fun (a, b) -> containsExpression a currentExpression)
            equalities
    match applicable with
    | [] -> l
    | _ ->
        let e1, e2 =
            (applicable
             |> List.toArray
             |> Array.sampleOne)

        let expressionNew = replaceExpression e2 e1 currentExpression
        if currentExpression = expressionNew then l
        else
        let t = sprintf "substitute: replace %s with %s in %s" (e1.ToFormattedString()) (e2.ToFormattedString()) (currentExpression.ToFormattedString())
        (currentExpression, expressionNew, t)::l

let mutate3 eqs l = 
    if random.NextDouble() < 0.5 then mutate eqs l 
    else 
        let (_, currentExpression,_) = List.head l
        let f, s = Array.sampleOne options3
        let nextexpr = f currentExpression
        let q  = s 
        if nextexpr = currentExpression then l
        else 
            (currentExpression, nextexpr,s)::l
 
eqs3 |> List.map (Equation >> string)

let pr3 = Distributions.uniform [|[(x2,e3, "")]; [x,eb,""]|]
let scorerz l = 
    let (_, e,_) = List.head l
    let w = float (width e)
    1./(averageDepth e )


let zt3 =
    pr3 |> sequenceSamples 0.4 (mutate3 eqs3) scorerz 100 50
   
zt3.SampleN(200) |> Array.maxBy (scorerz) |> List.map (fun (a,b,c) -> Equation(a,b).ToString(), c) |> List.rev
let zz = grad (prob x)/(grad (ln (prob x)))
let ee = expectation (prob x) e1
mapfirst rewriteExpectationAsIntegral  e3 |> bringIntegralOutGradient |> Expression.toFormattedString
(mapfirst rewriteExpectationAsIntegral e3) |> replaceExpression zz (prob x) |> Expression.toFormattedString
mapfirst rewriteExpectationAsIntegral  e3

mapfirst rewriteExpectationAsIntegral  e3 |> bringIntegralOutGradient 

Structure.collectIdentifiers e3
Expression.evaluateFloat