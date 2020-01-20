namespace MathNet.Symbolics
open Hansei.Continuation
open NumberTheory
open Utils   

module Expression =    
    open Core
    open Hansei.Core
    open Hansei.Core.Distributions  
    
    let shrink options sizeConstrain n e =
        let maxwidth = Structure.width e
        let mutable topwidth = maxwidth
        let rec loop steps n e =
            cont {
                if n = 0 then
                    do! constrain (sizeConstrain e)
                    return e,
                           List.rev steps
                           |> String.concat "\n\n"
                else
                    let! op, desc = uniform options
                    let e' = op e
                    do! constrain (e' <> e && Structure.width e' < maxwidth)
                    topwidth <- min topwidth (Structure.width e')
                    let str =
                        sprintf "%s:  \n$%s$" desc (fmt e')
                    return! loop (str :: steps) (n - 1) e'
            }
        loop [] n e

module Replicator =
    open EvolutionaryBayes.ParticleFilters
    open EvolutionaryBayes.Helpers
    open EvolutionaryBayes.ProbMonad
    open EvolutionaryBayes
    open Distributions
    open Core
    open Prelude.Common
    open Prelude.Math
    open EvolutionaryBayes.RegretMinimization
    open MathNet.Symbolics.Utils

    type ExpressionEvolver(equalities, options, startExpression, scorer, ?maxwidth, ?exploresteps) =
        let maxw = defaultArg maxwidth 50
        let learnsteps = defaultArg exploresteps 1000.

        let reward (action, (choice, ok, width)) =
            let w = scaleTo -1. 1. (float maxw) 0. width
            if choice = action && not ok then -1. 
            elif choice = action && ok then w
            else 0. 

        let varprob =
            match equalities with
            | [] -> 0.
            | _ -> 0.5

        let containsLog =
            Structure.existsRecursive Expression.containsLog startExpression
        let containsTrig =
            Structure.existsRecursive Expression.containsTrig startExpression
        let choices =
            List.filter
                (fun (_ : Expression -> Expression, desc : string) ->
                not (Strings.strContainsOneOf [ "logarithm"; "trig" ] desc)
                || (desc.Contains "logarithm" && containsLog)
                || (desc.Contains "trig" && containsTrig)) options
            |> List.toArray
        
        //let expert = Expert(reward, Array.map snd choices)

        //let funclookup = Dict.ofSeq(Array.map swap choices) 
        //do expert.New 0

        let mutate (currentExpression, path, mem) =
            dist {
                let! replace = bernoulli varprob
                if replace then
                    let applicable =
                        List.filter
                            (fst >> flip Expression.containsExpression currentExpression)
                            equalities
                    match applicable with
                    | [] -> return (currentExpression, path, mem)
                    | _ ->
                        let! e1, e2 = uniform (List.toArray applicable)
                        let expressionNew =
                            Expression.replaceExpression e2 e1 currentExpression
                        if (expressionNew <> currentExpression
                            && Structure.width expressionNew < maxw
                            && List.exists
                                   ((=) (Expression.FullSimplify expressionNew))
                                   mem |> not) then
                            let msg =
                                sprintf "$= %s$  \nSince $%s = %s$\n\n"
                                    (expressionNew.ToFormattedString())
                                    (e1.ToFormattedString())
                                    (e2.ToFormattedString())
                            return (expressionNew, (msg :: path),
                                    Expression.FullSimplify expressionNew :: mem)
                        else return (currentExpression, path, mem)
                else
                    //let probs =
                    //    if expert.First().Total < learnsteps then
                    //        Array.zip expert.[0].Weights expert.Actions
                    //    else expert.WeightedActions()
                    let! op, desc = uniform choices
                    let nextExpression = op currentExpression
                    let isnotequal = nextExpression <> currentExpression
                    let width' = if isnotequal then Structure.width nextExpression else maxw
                    if isnotequal
                       && width' < maxw
                       && List.exists
                              ((=) (Expression.FullSimplify nextExpression)) mem
                          |> not then
                        let msg =
                            sprintf "%s:  \n$%s$\n\n" desc
                                (Expression.toFormattedString nextExpression)
                        
                        //expert.Learn 0 (desc, true, float (width'))
                        return (nextExpression, (msg :: path),
                                Expression.FullSimplify nextExpression :: mem)
                    else  
                        //expert.Learn 0 (desc, false, 0.)
                        return (currentExpression, path, mem)
            }

        //member __.Expert = expert

        //member __.SequenceSamples(?mutateprob, ?samplespergen,
        //                          ?generations) =
        //    expert.Forget()
        //    let mp = defaultArg mutateprob 0.4
        //    let samplespergen = defaultArg samplespergen 500
        //    let gens = defaultArg generations 50
        //    sequenceSamples mp (fun e -> (mutate e).Sample()) scorer
        //        samplespergen gens
        //        (uniform [| startExpression, [sprintf "Start: $%s$\n\n" (fmt startExpression)], [] |])

        //member __.SampleChain n =
        //    expert.Forget()
        //    MetropolisHastings.sample 1. scorer (fun e -> (mutate e).Sample())
        //        (uniform [| startExpression, [], [] |]) n
        //    |> Sampling.roundAndGroupSamplesWith id
        //    |> categorical2

        //member __.EvolveSequence(?mutateprob, ?maxpopsize, ?samplespergen,
        //                         ?generations) =
        //    expert.Forget()
        //    let mp = defaultArg mutateprob 0.4
        //    let maxpopsize = defaultArg maxpopsize 250
        //    let samplespergen = defaultArg samplespergen 500
        //    let gens = defaultArg generations 50

        //    let pops =
        //        evolveSequence mp maxpopsize [] (fun _ e -> (mutate e).Sample())
        //            scorer samplespergen gens
        //            (uniform [| startExpression, [], [] |])
        //        |> List.toArray
        //        |> Array.normalizeWeights
        //        |> categorical2
        //    dist { let! pop = pops
        //           let! memberx = pop
        //           return memberx }

        //member __.SampleFrom n (dist : Distribution<_>) =
        //    dist.SampleN(n)
        //    |> Array.map (fun x -> x, scorer x)
        //    |> Array.normalizeWeights
        //    |> Helpers.Sampling.compactMapSamples id
        //    |> Array.sortByDescending snd


module Searcher =
    open Core
    open Prelude.Common
    open Hansei.Core.Distributions
    open Hansei.Core
    open System
    open EvolutionaryBayes.RegretMinimization
    open Integration
    open Expression

    let dispMath x = "$" + x + "$"

    let findPathR (expert:RegretLearner<int,_,_>) maxwidth options transformer equalities targetCondition startExpression =
        let varprob =
            match equalities with
            | [] -> 0.
            | _ -> 0.5
        let sw = Diagnostics.Stopwatch()
        let containsLog = Structure.existsRecursive Expression.containsLog startExpression
        let containsTrig =
            Structure.existsRecursive Expression.containsTrig startExpression
        let options' =
            List.filter
                (fun (_, desc : string) ->
                not (Strings.strContainsOneOf [ "logarithm"; "trig" ] desc)
                || (desc.Contains "logarithm" && containsLog)
                || (desc.Contains "trig" && containsTrig)) options   
        
        expert.SetActions (List.toArray options' |> Array.map snd)
        expert.New 0

        let rec search steps strmem mem path currentExpression =
            cont {
                if targetCondition currentExpression then
                    let fsteps = List.rev steps
                    fsteps |> List.iter (fun step -> expert.Learn(0, (currentExpression, step)))
                    return currentExpression, List.rev path, fsteps
                else
                    let! replace = bernoulli varprob
                    if replace then
                        let applicable =
                            List.filter
                                (fst >> flip Expression.containsExpression currentExpression)
                                equalities
                        match applicable with
                        | [] -> return! search steps strmem mem path currentExpression
                        | _ ->
                            let! e1, e2 = uniform applicable
                            let expressionNew =
                                Expression.replaceExpression e2 e1 currentExpression
                            do! constrain
                                    (expressionNew <> currentExpression
                                     && Structure.width expressionNew < maxwidth
                                     && List.exists
                                            ((=) (Expression.FullSimplify
                                                    expressionNew)) mem |> not)
                            let str =
                                e1.ToFormattedString() + ","
                                + e2.ToFormattedString()
                            do! constrain (List.exists ((=) str) strmem |> not)
                            let msg =
                                sprintf "$= %s$  \nSince $%s = %s$\n\n"
                                    (expressionNew.ToFormattedString())
                                    (e1.ToFormattedString())
                                    (e2.ToFormattedString())
                            return! search steps (str :: strmem)
                                        (Expression.FullSimplify expressionNew
                                         :: mem) (msg :: path) expressionNew
                    else
                        sw.Restart()
                        let! (nextExpression, desc, good) = transformer options' mem
                                                                currentExpression
                        sw.Stop()
                        do! constrain (good)
                        let msg =
                            sprintf "%s:  \n$%s$\n\n" desc
                                (Expression.toFormattedString nextExpression)
                        return! search ((desc, sw.ElapsedMilliseconds)::steps) strmem
                                    (Expression.FullSimplify nextExpression :: mem)
                                    (msg :: path) nextExpression
            }
        search [] [] [] [ Expression.toFormattedString startExpression
                           |> dispMath
                           |> sprintf "\n\nStart: %s  \n" ] startExpression

    let findPathGen maxwidth options transformer equalities targetCondition startExpression =
        let varprob =
            match equalities with
            | [] -> 0.
            | _ -> 0.5

        let containsLog = Structure.existsRecursive Expression.containsLog startExpression
        let containsTrig =
            Structure.existsRecursive Expression.containsTrig startExpression
        let options' =
            List.filter
                (fun (_, desc : string) ->
                not (Strings.strContainsOneOf [ "logarithm"; "trig" ] desc)
                || (desc.Contains "logarithm" && containsLog)
                || (desc.Contains "trig" && containsTrig)) options
    
        let rec search strmem mem path currentExpression =
            cont {
                if targetCondition currentExpression then
                    return currentExpression, List.rev path
                else
                    let! replace = bernoulli varprob
                    if replace then
                        let applicable =
                            List.filter
                                (fst >> flip containsExpression currentExpression)
                                equalities
                        match applicable with
                        | [] -> return! search strmem mem path currentExpression
                        | _ ->
                            let! e1, e2 = uniform applicable
                            let expressionNew =
                                replaceExpression e2 e1 currentExpression
                            do! constrain
                                    (expressionNew <> currentExpression
                                     && Structure.width expressionNew < maxwidth
                                     && List.exists
                                            ((=) (Expression.FullSimplify
                                                    expressionNew)) mem |> not)
                            let str =
                                e1.ToFormattedString() + ","
                                + e2.ToFormattedString()
                            do! constrain (List.exists ((=) str) strmem |> not)
                            let msg =
                                sprintf "$= %s$  \nSince $%s = %s$\n\n"
                                    (expressionNew.ToFormattedString())
                                    (e1.ToFormattedString())
                                    (e2.ToFormattedString())
                            return! search (str :: strmem)
                                        (Expression.FullSimplify expressionNew
                                         :: mem) (msg :: path) expressionNew
                    else
                        let! (nextExpression, desc, good) = transformer options' mem
                                                                currentExpression
                        do! constrain (good)
                        let msg =
                            sprintf "%s:\n$%s$\n\n" desc
                                (Expression.toFormattedString nextExpression)
                        return! search strmem
                                    (Expression.FullSimplify nextExpression :: mem)
                                    (msg :: path) nextExpression
            }
        search [] [] [ Expression.toFormattedString startExpression
                       |> dispMath
                       |> sprintf "\n\nStart: %s  \n" ] startExpression

    let findPath options transformer equalities targetCondition startExpression =
        findPathGen 50 options transformer equalities targetCondition startExpression

    let uniformSamplerGen maxwidth options mem currentExpression =
        cont {
            let! op, desc = uniform options  
            let nextExpression = op currentExpression
            let ok =
                nextExpression <> currentExpression  
                && Structure.width nextExpression < maxwidth
                && (List.exists ((=) (Expression.FullSimplify nextExpression)) mem
                    |> not) 
            return (nextExpression, desc, ok)
        }

    let integralTerminationCondition e =
        Structure.existsRecursive (function
            | IsIntegral _ | IsExpectation _  -> true 
            | _ -> false) e |> not
     
    let shallowOptions =
        [ Structure.applyInFunction Algebraic.expand, "Expand"
          Structure.applyInFunction Rational.reduce, "Reduce fractions"
          Structure.applyInFunction Rational.rationalize, "rationalize terms"
          Structure.applyInFunction Rational.expand, "expand fractions" 
          Structure.applyInFunction Logarithm.expand, "apply logarithm product/quotient rule, expand"
          Structure.applyInFunction Logarithm.contract, "apply logarithm product/quotient rule, contract"
          Structure.applyInFunction Trigonometric.substitute, "substitute trig expression"
          Structure.applyInFunction Trigonometric.contract, "contract trig expression"
          Structure.applyInFunction Trigonometric.expand, "expand trig expression"
          Structure.applyInFunction Trigonometric.simplify, "simplify trig expression"
          Structure.applyInFunction Logarithm.powerRule, "apply logarithm power rule" 
          evalIntegral, "Calculate integral"
          Expression.simplify true, "simplify expression"  ]

    let inline fullsummaryList take f res =
        let psum = List.sumBy fst res
        let len = List.length res
        let take = defaultArg take len
        let lenmax = min take len

        let v, sffx =
            if len <> 1 then "are", "s."
            else "is", "."
        [ yield sprintf "There %s %d result%s" v len sffx
    
          for (i, (p, steps)) in List.zip [ 1..lenmax ] res.[..take - 1] ->
              sprintf "\n\n__Result %d__: Probability: %A | Relative %A. %s" i p
                  (p / psum) (f steps
                              |> String.concat "  \n") ] 

    let fullsummaryConditional conds f (res:(float*'a)list) =
        let summ = fullsummaryList None f res 
        let rec iter strs = function
            | [] -> strs |> List.rev |> String.concat "\n" 
            | f::fs -> let top = List.filter f (List.tail summ) |> List.head 
                       iter (top::strs) fs
        iter [List.head summ] conds

    let inline fullsummary take f res = fullsummaryList take f res |> String.concat "\n" 
 

    let findIntegral terminatewith substMaxWidth transformMaxWidth eqs options nsamples expr =
        Model.ImportanceSample
            (findPathGen substMaxWidth options (uniformSamplerGen transformMaxWidth)
                 eqs terminatewith expr, nsamples = nsamples, maxdepth = 50)
        |> ProbabilitySpace.mapValues id
        |> List.sortByDescending fst

    type SmartIntegrator () =
        static member Integrate(expr, ?substMaxWidth, ?transformMaxWidth, ?eqs, ?options, ?nsamples) =
            findIntegral integralTerminationCondition (defaultArg substMaxWidth 25)
                (defaultArg transformMaxWidth 25) (defaultArg eqs []) (defaultArg options shallowOptions)
                    (defaultArg nsamples 100) expr