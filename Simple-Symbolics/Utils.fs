module MathNet.Symbolics.Utils

open MathNet.Symbolics
open System
open Microsoft.FSharp 
open Prelude.Math
open Prelude.Common

type TraceExplain<'a> =
     | Str of string
     | Op of ('a -> 'a) 
     | Instr of ('a -> 'a) * string

module List =
    let filterMap filter map xs =
        [ for x in xs do
              if filter x then yield map x ]

let [<Literal>] InfixFormat = "Infix"

let mutable expressionFormater = Infix.format
let mutable expressionFormat = "Infix"

let space() = if expressionFormat = InfixFormat then " " else " \\; "
let newline() = if expressionFormat = InfixFormat then "\n" else "\n \\\\ "
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
    member __.Trace = trace
    override __.ToString() =
        String.concat "\n\n" trace 

let stepTracer isverbose iseq fmt current instructions =
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
                              [ (if isverbose || cnt = 1 then fmt current else space())
                                nline
                                fmt next ])
                    next
                | Instr(f, s) ->
                    let next = f current
                    steps.Add(string cnt + ": " + s + ":\n\n${0}${1}$\\Longrightarrow {2}$",
                              [ (if isverbose || cnt = 1 then fmt current else space())
                                nline
                                fmt next ])
                    next
            loop (cnt + 1) next rest
    loop 1 current instructions 

let expressionTrace = stepTracer true false fmt
 
let safeEval f x = try f x with _ -> x
let flip f a b = f b a
let swap (a,b) = (b,a)
let fst3 (a, _, _) = a
let pairmap f (x, y) = f x, f y
let max2 (a,b) = max a b
let ignoreFirst f _ = f
let signstr x = if x < 0. then "-" else ""

module Hashset =
    let union (h1:Hashset<_>) h2 = h1.UnionWith(h2); h1

module Option =
    let mapOrAdd def f =
        function
        | None -> Some def
        | Some y -> Some(f y)

let inline absf x = Core.Operators.abs x
let inline logf x = Core.Operators.log x
let inline expf x = Core.Operators.exp x
let inline log10f x = Core.Operators.log10 x

let smartroundEx n x =
    if x > -1. && x < 1. && x <> 0. then
        let p = log10f (absf x)
        let roundto = int (ceil -p) + n
        if roundto > 15 then x, roundto
        else Math.Round(x, roundto), roundto
    else Math.Round(x, n), n

let smartround2 r x =
    if absf x < 1. then 
        let p = (log10f (absf x)) |> absf |> ceil
        let pten = 10. ** p
        let x' = x * pten
        (round r x')/pten
    else round r x
    
let smartround n = smartroundEx n >> fst

let real x = Approximation (Real x)

let todecimal = function | Number n -> real(float n) | f -> f
let todecimalr r = function | Number n -> real(float n |> Prelude.Common.round r) | f -> f
let degreeToRadians deg = 1/180Q * Operators.pi * deg
let radiansToDegree rad = (180Q * rad)/Operators.pi
//========================

let grad x = FunctionN(Gradient, [x])
let gradn var x = FunctionN(Gradient, [x;var] )
let diff dx x = FunctionN(Derivative, [x;dx])
let pdiff dx x = FunctionN(PartialDerivative, [x;dx]) 

let (|IsDerivative|_|) = function
     | FunctionN(PartialDerivative, [ x; dx ])
     | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
     | _ -> None  

let (|IsDerivativeStrict|_|) = function
    | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
    | _ -> None   

let func f = FunctionN(Function.Func, [Operators.symbol f])
let funcx f x = FunctionN(Function.Func, [Operators.symbol f;x])
let fx x = FunctionN(Function.Func, [Operators.symbol "f";x]) 
let fn x expr = FunctionN(Function.Func, [Operators.symbol "f";x; expr]) 
let fxn f x expr = FunctionN(Function.Func, [Operators.symbol f;x; expr]) 
let limit var lim x = FunctionN(Limit, [var;lim;x]) 
let hold x = Id x
let negateId x = (Operators.negate(Algebraic.expand(Operators.negate x)))

let (|IsFunction|_|) = function
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,fx)
    | _ -> None  

let (|IsFunctionWithParams|_|) = function
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,Some fx)
    | FunctionN(Func, [ f;x ]) -> Some(f,x,None)
    | _ -> None       
//===
 


//querying OEIS http://oeis.org/search?fmt=text&q=3,5,7,9,11&start=10