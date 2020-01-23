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
               
module Hashset =
    let union (h1:Hashset<_>) h2 = h1.UnionWith(h2); h1

module Option =
    let mapOrAdd def f =
        function
        | None -> Some def
        | Some y -> Some(f y) 

let safeEval f x = try f x with _ -> x
let flip f a b = f b a
let swap (a,b) = (b,a)
let fst3 (a, _, _) = a
let pairmap f (x, y) = f x, f y
let max2 (a,b) = max a b
let ignoreFirst f _ = f
let signstr x = if x < 0. then "-" else ""

let [<Literal>] InfixFormat = "Infix"

let mutable expressionFormater = Infix.format
let mutable expressionFormat = "Infix"

let space() = if expressionFormat = InfixFormat then " " else " \\; "
let newline() = if expressionFormat = InfixFormat then "\n" else "\n \\\\ "
let fmt e = expressionFormater e

let symbol = Operators.symbol

let setInfix() =
    expressionFormat <- "Infix"
    expressionFormater <- Infix.format
    
let setLatex() =
    expressionFormat <- "Latex"
    expressionFormater <- LaTeX.format 

//========================

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
 
//======================== 

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

//========================

let real x = Approximation (Real x)

let todecimal = function | Number n -> real(float n) | f -> f
let todecimalr r = function | Number n -> real(float n |> Prelude.Common.round r) | f -> f

let degreeToRadians deg = 1/180Q * Operators.pi * deg
let radiansToDegree rad = (180Q * rad)/Operators.pi

//========================

module Constants =
    open Operators
    let π = pi
    let pi = pi 
    let e = Constant Constant.E
     

[<RequireQualifiedAccess>]
type FuncType =
     | Identity 
     | Power of Expression
     | Function of Function
     member t.WrapExpression e =
        match t with 
        | Power n -> Expression.Power(e, n)
        | Function f -> Expression.Function(f, e)
        | Identity -> e
     override t.ToString() =
        match t with 
        | Power n -> " _ ^" + (expressionFormater n)
        | Function f -> string f
        | Identity -> "id" 

let grad x = FunctionN(Gradient, [x])
let gradn var x = FunctionN(Gradient, [x;var] )
let diff dx x = FunctionN(Derivative, [x;dx])
let pdiff dx x = FunctionN(PartialDerivative, [x;dx]) 

let func f = FunctionN(Function.Func, [Operators.symbol f])
let funcx f x = FunctionN(Function.Func, [Operators.symbol f;x])
let fx x = FunctionN(Function.Func, [Operators.symbol "f";x]) 
let fn x expr = FunctionN(Function.Func, [Operators.symbol "f";x; expr]) 
let fxn f x expr = FunctionN(Function.Func, [Operators.symbol f;x; expr]) 

let choose n k = FunctionN(Choose, [n;k])
let binomial n k = FunctionN(Choose, [n;k])
let prob x = FunctionN(Probability, [symbol "P"; x ])
let probc x param = FunctionN(Probability, [ symbol "P"; x; param ])
let probparam x param = FunctionN(Probability, [symbol "P";  x; param; 0Q ])

let expectation distr x = FunctionN(Function.Expectation, [ x; distr ])


let limit var lim x = FunctionN(Limit, [var;lim;x]) 

let hold x = Id x

let removeHold = function
    | Id x -> x
    | x -> x

let negateId x = (Operators.negate(Algebraic.expand(Operators.negate x))) 

let matrix x = Generic(x,GenericExpressionType.Matrix)

let vec x = Generic(x,GenericExpressionType.Vector)

let transpose x = Function(Transpose, x)

let inverse x = Function(Inverse, x)

let interval a b = IntSharp.Types.Interval.FromInfSup(a,b)

let isSpecializedFunction = function
    | Probability
    | Gradient
    | Integral 
    | Expectation -> true
    | _ -> false  

let (|IsFunctionExpr|_|) = function
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,fx)
    | _ -> None  

let (|IsFunctionExprWithParams|_|) = function
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,Some fx)
    | FunctionN(Func, [ f;x ]) -> Some(f,x,None)
    | _ -> None      

let (|IsDerivative|_|) = function
     | FunctionN(PartialDerivative, [ x; dx ])
     | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
     | _ -> None  

let (|IsDerivative1D|_|) = function
    | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
    | _ -> None    

let (|AsFunction|_|) input = 
     match input with 
     | Function(f, x) -> Some(FuncType.Function f,x)
     | Power(x,n) -> Some(FuncType.Power n,x)
     | f -> Some(FuncType.Identity, f)

let (|IsProb|_|) input = 
     match input with 
     | FunctionN(Probability, _::x::_) -> Some(x) 
     | _ -> None

let (|IsExpectation|_|) input = 
     match input with 
     | FunctionN(Function.Expectation, [x; p]) -> Some(x, p) 
     | _ -> None  

let (|Binomial|_|) input =
     match input with
     | FunctionN(Choose, [n;k]) -> Some(n,k)
     | _ -> None 

//========================
 