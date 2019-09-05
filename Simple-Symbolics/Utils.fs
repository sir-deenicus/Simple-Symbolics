module MathNet.Symbolics.Utils

open MathNet.Symbolics
open System

open FSharp.Data 
open Prelude.Math
open Prelude.Common

type TraceExplain<'a> =
     | Str of string
     | Op of ('a -> 'a) 
     | Instr of ('a -> 'a) * string

let [<Literal>] InfixFormat = "Infix"

let mutable expressionFormater = Infix.format
let mutable expressionFormat = "Infix"
let space() = if expressionFormat = InfixFormat then " " else " \\; "
let fmt e = expressionFormater e

let setInfix() =
    expressionFormat <- "Infix"
    expressionFormater <- Infix.format
    
let setLatex() =
    expressionFormat <- "Latex"
    expressionFormater <- LaTeX.format


type StepTrace(s) =
    let trace = Hashset()
    do trace.Add s |> ignore
    member __.Add e =
        trace.Add(sprintf "$%s$" (expressionFormater e)) |> ignore
    member __.Add e = trace.Add(sprintf "$%s$" (e.ToString())) |> ignore
    member __.Add s = trace.Add(s) |> ignore
    member __.Add (s, asText, parameters) = 
        String.Format(s, Seq.toArray parameters 
                        |> Array.map (asText>>fun a -> a:>obj)) 
        |> trace.Add 
        |> ignore
    member __.Add (s, parameters) = 
        String.Format(s, Seq.toArray parameters) 
        |> trace.Add 
        |> ignore
    override __.ToString() =
        String.concat "\n\n" trace
         

let stepTracer iseq fmt current instructions =
    let steps = StepTrace("")
    let nline = if iseq then "\n\n  " else "  "
    let rec loop cnt current =
        function
        | [] -> current, steps
        | step :: rest ->
            let next =
                match step with
                | Str s ->
                    steps.Add(string cnt + ": " + s)
                    current
                | Op f ->
                    let next = f current
                    steps.Add(string cnt + ": ${0}${1}$\\Longrightarrow {2}$",
                              [ fmt current
                                nline
                                fmt next ])
                    next
                | Instr(f, s) ->
                    let next = f current
                    steps.Add(string cnt + ": " + s + ":\n\n${0}${1}$\\Longrightarrow {2}$",
                              [ fmt current
                                nline
                                fmt next ])
                    next
            loop (cnt + 1) next rest
    loop 1 current instructions
     

let expressionTrace = stepTracer false fmt
 
let safeEval f x = try f x with _ -> x
let flip f a b = f b a
let swap (a,b) = (b,a)
let fst3 (a, _, _) = a
let pairmap f (x, y) = f x, f y
let max2 (a,b) = max a b
let ignoreFirst f _ = f
let signstr x = if x < 0. then "-" else ""

module Option =
    let mapOrAdd def f =
        function
        | None -> Some def
        | Some y -> Some(f y)

let smartroundEx n x =
    if x > -1. && x < 1. && x <> 0. then
        let p = log10 (abs x)
        let roundto = int (ceil -p) + n
        if roundto > 15 then x, roundto
        else Math.Round(x, roundto), roundto
    else Math.Round(x, n), n

let smartround2 r x =
    if abs x < 1. then 
        let p = (log10 (abs x)) |> abs |> ceil
        let pten = 10. ** p
        let x' = x * pten
        (round r x')/pten
    else round r x
    
let smartround n = smartroundEx n >> fst

let real x = Approximation (Real x)

let todecimal = function | Number n -> real(float n) | f -> f
let todecimalr r = function | Number n -> real(float n |> Prelude.Common.round r) | f -> f

//========================
let currencycacheloc = "currencycache.json"

type CurrencyProvider = FSharp.Data.JsonProvider<"currencyTemplate.json">

let downloadCurrencyRates() =
    use wc = new Net.WebClient()
    try
        let data =
            wc.DownloadData "https://www.mycurrency.net/US.json"
            |> Strings.DecodeFromUtf8Bytes
        IO.File.WriteAllText(currencycacheloc, data)
        data
        |> CurrencyProvider.Parse
        |> Some
    with _ ->
        if IO.File.Exists currencycacheloc then
            IO.File.ReadAllText currencycacheloc
            |> CurrencyProvider.Parse
            |> Some
        else None

let currencyMap =
    match downloadCurrencyRates() with
    | None -> Map.empty
    | Some currencyRates ->
        currencyRates.Rates
        |> Array.map (fun r ->
               r.CurrencyCode,
               (1M / r.Rate)
               |> float
               |> smartround2 2)
        |> Map
