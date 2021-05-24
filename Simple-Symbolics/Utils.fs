/// <summary>
///  Core Util functions.
/// </summary>
///
/// <namespacedoc>
///   <summary>Extension to MathNet.Symbolics which allows for flexible descriptions of and computations on symbolic math expressions.</summary>
///
///   <remarks>Simple Symbolics is a library built atop MathNet Symbolics. It is not meant to be a replacement for computer algebra systems. Such systems are largely automatic and quite heavyweight. This project intends to diverge a bit from typical CAS to look at what happens when you simply automate tedium and slightly augment a human? The manipulations are meant as much as possible to mirror what a human would do. The code can thus serve as a description of how humans typically approach these problems. Otherwise, it also provide tools that can be combined to do so. An example is indefinite integration. CAS systems can in instances give very unintuitive answers or otherwise fail to complete where a human could. Another difference is the intention to combine with basic logic programming and serve as a note taking tool when reading mathematical papers. This system will then augment the working memory for the reader but also (end goal) allow manipulation of some of the claims.</remarks>
/// </namespacedoc>
module MathNet.Symbolics.Utils

open MathNet.Symbolics
open System
open Microsoft.FSharp
open Prelude.Math
open Prelude.Common
open MathNet.Numerics

type TraceExplain<'a> =
     | Str of string
     | Op of ('a -> 'a)
     | Instr of ('a -> 'a) * string

module List =
    let filterMap filter map xs =
        [ for x in xs do
            if filter x then yield map x ]

    let removeDuplicates (xs:_ list) = List.ofSeq (Hashset(xs))

module Hashset =
    let union (h1:Hashset<_>) h2 = h1.UnionWith(h2); h1

module Option =
    let mapOrAdd def f =
        function
        | None -> Some def
        | Some y -> Some(f y)

module Constants =
    open Operators
    let π = pi
    let pi = pi
    let e = Constant Constant.E
    let i = Constant Constant.I

let ⅈ = Constants.i
let ⅇ = Constants.e
let π = pi

let safeEval f x = try f x with _ -> x
let flip f a b = f b a
let swap (a,b) = (b,a)
let fst3 (a, _, _) = a
let pairmap f (x, y) = f x, f y
let max2 (a,b) = max a b
let ignoreFirst f _ = f
let signstr x = if x < 0. then "-" else ""

let [<Literal>] InfixFormat = "Infix"
let [<Literal>] LatexFormat = "Latex"

let mutable expressionFormater = Infix.format
let mutable expressionFormat = "Infix"

let space() = if expressionFormat = InfixFormat then " " else " \\; "
let newline() = if expressionFormat = InfixFormat then "\n" else "\n \\\\ "
let notequalStr() = if expressionFormat = InfixFormat then "<>" else " \\neq; "

let leftBrackets s = if expressionFormat = InfixFormat then "[" else "\\left" + s
let rightBrackets s = if expressionFormat = InfixFormat then "]" else "\\right" + s

let leftBrace () = leftBrackets "\\{"
let rightBrace () = rightBrackets "\\}"

let leftBracket () = leftBrackets "\\["
let rightBracket () = rightBrackets "\\]"

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
    let nline = if iseq then "\n  " else "  "
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

let expressionTracer expr instrs = stepTracer true false fmt expr (List.map Op instrs)

//========================

let inline absf x = Core.Operators.abs x
let inline logf x = Core.Operators.log x
let inline expf x = Core.Operators.exp x
let inline log10f x = Core.Operators.log10 x
let inline sqrtf x = Core.Operators.sqrt x
let ceilf x = FSharp.Core.Operators.ceil x
let floorf x = FSharp.Core.Operators.floor x

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
let ofRational r = Expression.FromRational r
let ofInteger i = Expression.FromInt32 i
let ofBigInteger i = Expression.FromInteger i

let ofFloat x = Approximation (Real x)
let todecimal = function | Number n -> ofFloat(float n) | f -> f
let todecimalr roundto = function | Number n -> ofFloat(float n |> Prelude.Common.round roundto) | f -> f

let degreeToRadians deg = 1/180Q * Operators.pi * deg
let radiansToDegree rad = (180Q * rad)/Operators.pi

module Approximations =
    let round n = function
        | Approximation(Real r) -> Approximation(Real (round n r))
        | x -> x

//========================

let functionFirstTermOnly = function
    | Gradient
    | Derivative
    | PartialDerivative
    | SumOver
    | ProductOver
    | Integral
    | Expectation -> true
    | _ -> false

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

module FunctionHelpers =
    ///Create a function symbol with name and parameter symbol `x`: fn "g" y = `g(y)`
    let fn name x = FunctionN(Function.Func, [Operators.symbol name;x])
    ///Create a function symbol with default name "f": fx y = `f(y)`
    let fx x = FunctionN(Function.Func, [Operators.symbol "f";x])
    ///Create a function with parameter, body and default name "f": fx2 x x^2 = `x |-> x^2`
    let fx2 x expr = FunctionN(Function.Func, [Operators.symbol "f";x; expr])
    ///Create a function with parameter, body and name : fxn "g" x x^2 = `x |-> x^2`
    let fxn name x expr = FunctionN(Function.Func, [Operators.symbol name;x; expr])

let grad x = FunctionN(Gradient, [x])
let gradn var x = FunctionN(Gradient, [x;var] )

///wrap input expression in Leibniz notation for differentiation.
let diff dx x = FunctionN(Derivative, [x;dx])

///use partial differentiation Leibniz notation
let pdiff dx x = FunctionN(PartialDerivative, [x;dx])

let gamma x = Function(Gamma,x)

let digamma x = Function(DiGamma, x)

let beta a b = FunctionN(Beta, [a;b])

let incompleteBeta a b x = FunctionN(InCompleteBeta, [a;b; x])

let regularizedBeta a b x = FunctionN(RegularizedBeta, [a;b; x])

let gammaln x = Function(Ln, (gamma x))

let facln x = exp (gammaln (x+1Q))
let fac x = Function(Fac, x)
let choose n k = FunctionN(Choose, [n;k])
let binomial n k = FunctionN(Choose, [n;k])
let prob x = FunctionN(Probability, [symbol "P"; x ])
let probn n x = FunctionN(Probability, [symbol n; x ])
let probc x theta = FunctionN(Probability, [ symbol "P"; x; theta ])
let probparam x theta = FunctionN(Probability, [symbol "P";  x; theta; Parameter ";" ])

let erf x = Function(Erf, x)

let inverf x = Function(ErfInv, x)

let expectation distr x = FunctionN(Function.Expectation, [ x; distr ])

let summation var start stop fx = FunctionN(SumOver, [fx;var;start;stop])

let products var start stop fx = FunctionN(ProductOver, [fx;var;start;stop])

let Σ var start stop fx = summation var start stop fx

let Π var start stop fx = products var start stop fx

let limit var lim x = FunctionN(Limit, [var;lim;x])

let matrix x = Generic(x,GenericExpressionType.Matrix)

let vec x = Generic(x,GenericExpressionType.Vector)

let transpose x = Function(Transpose, x)

let inverse x = Function(Inverse, x)

let super x superscript = FunctionN(SupIndexed, [x;superscript])

let sub x subscript = FunctionN(Indexed, [x; subscript])

let subs x subscripts = FunctionN(Indexed, x::subscripts)

let (^^) a b = super a b

let define a b = Definition(a,b, "")

///Define with left, right and description
let defineStr def = Definition def

let extractDefinition = function Definition(_,b, _) -> b | x -> x

let integral dx x = FunctionN(Integral, [ x; dx ])

let defintegral dx a b x = FunctionN(Integral, [ x; dx; a; b ])

let hold x = Id x

let cage x = Id x

let seal x = Id x

let ceil x = Function(Ceil, x)

let floor x = Function(Floor,x)

let customFunction s x = Function(CustomFunction s, x)

let customFunctionN s xs = FunctionN(CustomFunction s, xs)

module Hold =
    let extractLeadingNegative = function
        | Id(Product (Number n::_) as p) when n < 0N -> -1 * hold (p / -1)
        | x -> x

    let remove = function
        | Id x -> x
        | x -> x

//========================
let (|IsFunctionExpr|_|) = function
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,fx)
    | _ -> None

let (|IsFunctionExprNameOnly|_|) = function
    | FunctionN(Func, [ f;x ]) -> Some(f,x)
    | _ -> None

let (|IsFunctionExprAny|_|) = function
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,Some fx)
    | FunctionN(Func, [ f;x ]) -> Some(f,x,None)
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

let (|IsIntegral|_|) = function
     | FunctionN(Integral, [ x; dx ]) -> Some(x,dx)
     | _ -> None

let (|IsDefiniteIntegral|_|) = function
     | FunctionN(Integral, [ x; dx;a;b ]) -> Some(x,dx,a,b)
     | _ -> None

let (|IsDerivative|_|) = function
     | FunctionN(PartialDerivative as f, [ x; dx ])
     | FunctionN(Derivative as f, [ x; dx ]) -> Some(f, x,dx)
     | _ -> None

let (|IsTotalDerivative|_|) = function
    | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
    | _ -> None

let (|IsPartialDerivative|_|) = function
    | FunctionN(PartialDerivative, [ x; dx ]) -> Some(x,dx)
    | _ -> None

let (|IsLimit|_|) = function
    | FunctionN(Limit, [var;lim;x])  -> Some(var,lim,x)
    | _ -> None

///(fx,var,start, stop)
let (|Summation|_|) input =
     match input with
     | FunctionN(SumOver, [fx;var;start; stop]) -> Some(fx,var,start, stop)
     | FunctionN(SumOver, [fx]) -> Some(fx, symbol "", NegativeInfinity, PositiveInfinity)
     | FunctionN(SumOver, [fx; var]) -> Some(fx, var, NegativeInfinity, PositiveInfinity)
     | _ -> None

///(fx,var,start, stop)
let (|Products|_|) input =
    match input with
    | FunctionN(ProductOver, [fx;var;start; stop]) -> Some(fx,var,start, stop)
    | FunctionN(ProductOver, [fx]) -> Some(fx, symbol "", NegativeInfinity, PositiveInfinity)
    | FunctionN(ProductOver, [fx; var]) -> Some(fx, var, NegativeInfinity, PositiveInfinity)
    | _ -> None
//========================

let expectationsDistribution = function
    | IsExpectation (_, px) -> px
    | _ -> Undefined

let expectationsWithInnerProb = function
    | IsExpectation (_, IsProb x) -> x
    | _ -> Undefined

let innerProb = function
    | IsProb x -> x
    | _ -> Undefined

let isProb = function | IsProb _ -> true | _ -> false

let isExpectation = function IsExpectation _ -> true | _ -> false

//////////

let xor a b = (a && not b) || (not a && b)
