module MathNet.Symbolics.Utils

open MathNet.Symbolics
open System

type Hashset<'a> = System.Collections.Generic.HashSet<'a>

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

let ignoreFirst f _ = f
let signstr x = if x < 0. then "-" else ""

type MaybeBuilder() =
    member __.Bind(x, f) =
        match x with
        | Some(x) -> f(x)
        | _ -> None
    member __.Delay(f) = f()
    member __.Return(x) = Some x
    member __.ReturnFrom(x) = x

let maybe = MaybeBuilder()

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

let smartround n = smartroundEx n >> fst

