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

    let product xs ys =
        [ for x in xs do
            for y in ys do
                yield x, y ]

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


let mergeTwoListOfLists (l1:List<List<_>>) (l2:List<List<_>>) = List.map2 (fun a b -> a @ b) l1 l2

let mergeTwoArrayOfArrays (l1:_[][]) (l2:_[][]) = Array.map2 (fun a b -> Array.append a b) l1 l2

let xor a b = (a && not b) || (not a && b)

let inline pairwiseDiff sequence = sequence |> Seq.pairwise |> Seq.map (fun (a,b) -> b - a)


let [<Literal>] InfixFormat = "Infix"
let [<Literal>] LatexFormat = "Latex"

let mutable expressionFormater = Infix.format
let mutable expressionFormat = "Infix"

let space() = if expressionFormat = InfixFormat then " " else " \\; "
let newline() = if expressionFormat = InfixFormat then "\n" else "\n \\\\ "
let notequalStr() = if expressionFormat = InfixFormat then "<>" else " \\neq; "

let leftBrackets si s = if expressionFormat = InfixFormat then si else "\\left" + s
let rightBrackets si s = if expressionFormat = InfixFormat then si else "\\right" + s

let leftBrace () = leftBrackets "{" "\\{"
let rightBrace () = rightBrackets "}" "\\}"

let leftBracket () = leftBrackets "[" "\\["
let rightBracket () = rightBrackets "]" "\\]"

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
        trace.Add(sprintf "$$%s$$" (expressionFormater e)) |> ignore
    member __.Add e = trace.Add(sprintf "$$%s$$" (e.ToString())) |> ignore
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

let expressionTrace = stepTracer false false fmt

let expressionTracer expr instrs = stepTracer false false fmt expr (List.map Op instrs)

//let expressionTracer expr instrs = stepTracer false false fmt expr (List.map Op instrs)
let expressionInstrTracer expr instrs = stepTracer false false fmt expr (List.map Instr instrs)

type Expression with
    static member Trace(instrs : _ list, expr:Expression) =
        stepTracer false false fmt expr (List.map Instr instrs)

    static member Trace(instrs : _ list, expr:Expression) =
        stepTracer false false fmt expr (List.map Op instrs)
         
    member expr.Trace(instrs : _ list) =
        stepTracer false false fmt expr (List.map Op instrs)

    member expr.Trace(instrs : _ list) =
        stepTracer false false fmt expr (List.map Instr instrs)
        
//========================

let inline absf x = Core.Operators.abs x
let inline logf x = Core.Operators.log x
let inline expf x = Core.Operators.exp x
let inline log10f x = Core.Operators.log10 x
let inline sqrtf x = Core.Operators.sqrt x
let inline sinf x = Core.Operators.sin x
let inline cosf x = Core.Operators.cos x
let inline tanf x = Core.Operators.tan x
let inline acosf x = Core.Operators.acos x
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
let inline ofDecimal d = ofRational (BigRational.FromDecimal (decimal d))
let ofFloat x = Approximation (Real x)

let numToDecimal = function | Number n -> ofFloat(float n) | f -> f
let numToDecimalr roundto = function | Number n -> ofFloat(float n |> Prelude.Common.round roundto) | f -> f
let intervalF a b = IntervalF (IntSharp.Types.Interval.FromInfSup(a,b))
let intervalFloat(a,b) = IntSharp.Types.Interval.FromInfSup(a,b)
let interval a b = Interval (a,b)

let degreeToRadians deg = 1/180Q * Operators.pi * deg
let radiansToDegree rad = (180Q * rad)/Operators.pi
 
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

[<RequireQualifiedAccess>]
module Fn =
    ///Create a function symbol with name and parameter symbol `x`: fn "g" y = `g(y)`
    let fn name x = FunctionN(Function.Func, [Operators.symbol name;x])
    ///Create a function symbol with default name "f": fx y = `f(y)`
    let fx x = FunctionN(Function.Func, [Operators.symbol "f";x])
    ///Create a function with parameter, body and default name "f": fx2 x x^2 = `x |-> x^2`
    let fx2 x expr = FunctionN(Function.Func, [Operators.symbol "f";x; expr])
    ///Create a function with parameter, body and name : fxn "g" x x^2 = `x |-> x^2`
    let fxn name x expr = FunctionN(Function.Func, [Operators.symbol name;x; expr])

 
type Fn() =
    ///Create a function symbol with name and parameter symbol `x`: fn "g" y = `g(y)`
    static member fx(name, x) = FunctionN(Function.Func, [Operators.symbol name;x])
    static member fx(xs: Expression list, expr) = 
        FunctionN(Function.Func, [Operators.symbol "f"; Tupled xs; expr]) 
    static member fx(name, xs:Expression list, expr:Expression) = 
        FunctionN(Function.Func, [Operators.symbol name; Tupled xs; expr]) 
    ///Create a function symbol with default name "f": fx y = `f(y)`
    static member fx x = FunctionN(Function.Func, [Operators.symbol "f";x])
    ///Create a function with parameter, body and default name "f": fx x x^2 = `x |-> x^2`
    static member fx(x, expr) = FunctionN(Function.Func, [Operators.symbol "f";x; expr])
    ///Create a function with parameter, body and name : fx "g" x x^2 = `x |-> x^2`
    static member fx(name, x, expr) = FunctionN(Function.Func, [Operators.symbol name;x; expr])

let grad0 x = FunctionN(Gradient, [x])

let grad var x = FunctionN(Gradient, [x;var] )

///wrap input expression in Leibniz notation for differentiation.
let diff dx x = FunctionN(Derivative, [x;dx])

///wrap input expression in Leibniz notation for differentiation with respect to the nth variable
let diffnth n dx x = FunctionN(Derivative, [x;dx;n])

///use partial differentiation Leibniz notation
let pdiff dx x = FunctionN(PartialDerivative, [x;dx])

///a partial derivative with respect to the nth variable
let pdiffnth n dx x = FunctionN(PartialDerivative, [x;dx;n])

let gamma x = Function(Gamma,x)

let digamma x = Function(DiGamma, x)

let beta a b = FunctionN(Beta, [a;b])

let incompleteBeta a b x = FunctionN(InCompleteBeta, [a;b; x])

let regularizedBeta a b x = FunctionN(RegularizedBeta, [a;b; x])

let gammaln x = Function(Ln, (gamma x))

let facGamma x = gamma (x+1Q)
let facln x = gammaln (x+1Q)
let fac x = Function(Fac, x)
let choose n k = FunctionN(Choose, [n;k])
let binomial n k = FunctionN(Choose, [n;k])
let prob x = FunctionN(Probability, [symbol "P"; x ])
let probn n x = FunctionN(Probability, [symbol n; x ])
let probc x theta = FunctionN(Probability, [ symbol "P"; x; theta ])
let probcn n x theta = FunctionN(Probability, [ symbol n; x; theta ])
let probparam x theta = FunctionN(Probability, [symbol "P";  x; theta; Parameter ";" ])
let probparamn s x theta = FunctionN(Probability, [symbol s;  x; theta; Parameter ";" ])

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

let tuple x = Tupled(x)

let (^) a b = super a b

let define a b = Definition(a,b, "")

open type Fn
let q = symbol "q"
let qq = fx (tuple[q;q], q + q)

///Define with left, right and description
let defineStr def = Definition def

let extractDefinition = function Definition(_,b, _) -> b | x -> x

let integral dx x = FunctionN(Integral, [ x; dx ])

let defintegral dx a b x = FunctionN(Integral, [ x; dx; a; b ])

let hold x = Id (x,"")

let taghold s x = Id(x,s)

let cage x = hold x

let seal x = hold x

let ceil x = Function(Ceil, x)

let floor x = Function(Floor,x)

///isolate "extracts" exprToIsolate from expr by dividing expr by exprToIsolate
///applying hold to that result and multiplying the result by exprToIsolate
///This is useful for keeping vector type variables from mixing with exressions
let isolate (exprToIsolate) expr =
    hold(expr/exprToIsolate) * exprToIsolate

///isolate "extracts" exprToIsolate from expr by dividing expr by exprToIsolate
///applying hold to that result and multiplying the result by exprToIsolate
///This is useful for keeping vector type variables from mixing with exressions
///This version adds a tag to the sealed variable. Tagged variables aren't simplified by default and require fullsimplify to be removed. They can allow more precise editing of expressions.
let isolateTagged (exprToIsolate) tag expr =
    taghold tag (expr/exprToIsolate) * exprToIsolate

///holdAndIsolate is a common pattern where we eg multiply by a quantity we want to keep isolated.
///it take a binary function f, (such as multiplication) and apply it as f a (hold b) |> isolate (hold b)
let holdAndIsolate f a b = f a (hold b) |> isolate (hold b)

///holdAndIsolate is a common pattern where we eg multiply by a quantity we want to keep isolated.
///it take a binary function f, (such as multiplication) and apply it as f a (hold b) |> isolate (hold b)
///This version adds a tag to the sealed variable. Tagged variables aren't simplified by default and require fullsimplify to be removed. They can allow more precise editing of expressions.
let holdAndIsolateTagged f tag a b = f a (taghold tag b) |> isolate (taghold tag b)

///this is just a function that holds a and b and multiplies them. hold keeps them from being simplified 
let dot a b = hold a * (repeat 2 hold b) //repeat 2 for the case a = b

module Hold =
    let extractLeadingNegative = function
        | Id(Product (Number n::_) as p, _) when n < 0N -> -1 * hold (p / -1)
        | x -> x

    let remove = function
        | Id (x, _) -> x
        | x -> x
  
module Tuples =
    /// <summary>
    /// Computes the Cartesian product of two expressions, handling both tupled and non-tupled inputs.
    /// </summary>
    /// <param name="a">First expression (can be a tuple or single value)</param>
    /// <param name="b">Second expression (can be a tuple or single value)</param>
    /// <returns>A tupled expression containing all possible pairs from inputs</returns>
    /// <remarks>
    /// Handles four cases:
    /// 1. (a₁,a₂) × (b₁,b₂) → ((a₁,b₁),(a₁,b₂),(a₂,b₁),(a₂,b₂))
    /// 2. (a₁,a₂) × b → ((a₁,b),(a₂,b))
    /// 3. a × (b₁,b₂) → ((a,b₁),(a,b₂))
    /// 4. a × b → (a,b)
    /// 
    /// Examples:
    /// - cartesianProduct (tuple [x;y]) (tuple [1;2]) = tuple [(x,1);(x,2);(y,1);(y,2)]
    /// - cartesianProduct (tuple [x;y]) z = tuple [(x,z);(y,z)]
    /// - cartesianProduct x (tuple [1;2]) = tuple [(x,1);(x,2)]
    /// - cartesianProduct x y = tuple [x;y]
    /// </remarks> 
    let cartesianProduct (a:Expression) (b:Expression) = 
        let inline product l1 l2 = 
            List.product l1 l2
            |> List.map (fun (a,b) -> tuple [a;b])
            |> tuple
        match a, b with
        | Tupled l1, Tupled l2 -> product l1 l2
        | Tupled l1, b -> product l1 [b]
        | a, Tupled l2 -> product [a] l2
        | _ -> tuple [a;b]
                
    /// <summary>
    /// Combines two expressions into a single tupled expression, handling both tupled and non-tupled inputs.
    /// </summary>
    /// <param name="a">First expression (can be a tuple or single value)</param>
    /// <param name="b">Second expression (can be a tuple or single value)</param>
    /// <returns>A tupled expression containing all elements from both inputs in sequence</returns>
    /// <remarks>
    /// Handles four cases:
    /// 1. (a₁,a₂) ⊕ (b₁,b₂) → (a₁,a₂,b₁,b₂)
    /// 2. (a₁,a₂) ⊕ b → (a₁,a₂,b)
    /// 3. a ⊕ (b₁,b₂) → (a,b₁,b₂)
    /// 4. a ⊕ b → (a,b)
    /// 
    /// Examples:
    /// - combine (tuple [x;y]) (tuple [1;2]) = tuple [x;y;1;2]
    /// - combine (tuple [x;y]) z = tuple [x;y;z]
    /// - combine x (tuple [1;2]) = tuple [x;1;2]
    /// - combine x y = tuple [x;y]
    /// </remarks>
    let combine (a:Expression) (b:Expression) =
        match a, b with
        | Tupled l1, Tupled l2 ->
            Tupled (l1 @ l2)
        | Tupled l1, b -> 
            Tupled (l1 @ [b])
        | a, Tupled l2 ->
            Tupled (a::l2) 
        | _ -> Tupled [a;b]
         
//========================

/// <summary>
/// Active pattern that matches function expressions and extracts the function and argument information.
/// </summary>
/// <remarks>
/// This pattern matches expressions of the form:
/// - FunctionN(Func, [f;x;fx]) where:
///   f is the function name/identifier
///   x is the parameter(s)
///   fx is the function body
/// 
/// Returns:
/// - Some(f,x,fx) when matched
/// - None when not a function expression
/// 
/// Examples:
/// - f(x) = x + 1 matches as Some(f, x, x+1)
/// - f(x,y) = x*y matches as Some(f, (x,y), x*y) 
/// - 2+2 returns None
/// </remarks>
let (|IsFunctionExpr|_|) = function 
    | FunctionN(Func, [ f;x; fx ]) -> Some(f,x,fx)
    | _ -> None

/// This active pattern matches a function expression with only the function name and its argument.
/// It returns a tuple with the function name and its argument.
/// If the input does not match this pattern, it returns None.
let (|IsFunctionExprNameOnly|_|) = function
    | FunctionN(Func, [ f;x ]) -> Some(f,x)
    | _ -> None
    
let (|IsFunctionExprAny|_|) = function
    | FunctionN(Func, [ f; x; fx ]) -> Some(f,x,Some fx)
    | FunctionN(Func, [ f; x ]) -> Some(f,x,None)
    | _ -> None

let (|AsFunction|_|) input =
     match input with
     | Function(f, x) -> Some(FuncType.Function f,x)
     | Power(x,n) -> Some(FuncType.Power n,x)
     | f -> Some(FuncType.Identity, f)

/// This active pattern matches a Probability expression with only the function name and its argument (in that order)
let (|IsProb|_|) input =
    let inner = function  
        | FunctionN(Probability, nm::x::_) -> Some(nm, x) 
        | Product [FunctionN(Probability, nm::x::_); FunctionN(Probability, nm2::x2::_)] -> 
            Some (symbol $"{nm} and {nm2}", Tuples.combine x x2)
        | _ -> None
            
    match input with
     | Definition(px, _, _) -> inner px
     | px -> inner px

/// This active pattern matches a Conditional Probability expression with only the function name and its argument and the conditioned on variable
///  (in that order)
let (|IsCondProb|_|) input =
     match input with
     | FunctionN(Probability, [Identifier (Symbol nm); x; y]) -> Some(nm,x,y)
     | Definition(FunctionN(Probability, [Identifier (Symbol nm); x; y]), _, _) -> Some(nm,x,y)
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

let (|IsMatrix|_|) = function
     | Generic(x,GenericExpressionType.Matrix) -> Some(x)
     | _ -> None

let (|IsVector|_|) = function
    | Generic(x,GenericExpressionType.Vector) -> Some(x)
    | _ -> None

/// This active pattern matches a function expression with a derivative operator and its argument.
/// It returns a tuple with the derivative operator, the variable with respect to which the derivative is taken, and the differential.
/// If the input does not match this pattern, it returns None.
let (|IsDerivative|_|) = function
    | FunctionN(PartialDerivative as f, [ x; dx ])
    | FunctionN(Gradient as f, [x; dx])
    | FunctionN(Derivative as f, [ x; dx ]) -> Some(f, x,dx)
    | _ -> None

let (|IsNthDerivative|_|) = function
    | FunctionN(Derivative as f, [ x; dx; n ]) -> Some(f, x,dx,n)
    | FunctionN(PartialDerivative as f, [ x; dx; n ]) -> Some(f, x,dx,n)
    | _ -> None

let (|IsTotalDerivative|_|) = function
    | FunctionN(Derivative, [ x; dx ]) -> Some(x,dx)
    | _ -> None

let (|IsPartialDerivative|_|) = function
    | FunctionN(PartialDerivative, [ x; dx ]) -> Some(x,dx)
    | _ -> None

let (|IsGradient|_|) = function
    | FunctionN(Gradient, [ x; dx ]) -> Some(x,dx)
    | _ -> None

let (|IsLimit|_|) = function
    | FunctionN(Limit, [var;lim;x])  -> Some(var,lim,x)
    | _ -> None

///(fx,var,start, stop)
let (|Summation|_|) input =
     match input with
     | FunctionN(SumOver, [fx;var;start; stop]) -> Some(fx,var,start, stop)
     | _ -> None

///(fx, var)
let (|SummationVar|_|) input =
     match input with
     | FunctionN(SumOver, [fx;var]) -> Some(fx,var)
     | FunctionN(SumOver, [fx;var;_; _]) -> Some(fx,var)
     | _ -> None

///(fx)
let (|SummationTerm|_|) input =
     match input with
     | FunctionN(SumOver, [fx]) -> Some(fx)
     | FunctionN(SumOver, [fx;_;_;_]) -> Some(fx)
     | FunctionN(SumOver, [fx;_]) -> Some(fx)
     | _ -> None

///(fx,var,start, stop)
let (|Products|_|) input =
    match input with
    | FunctionN(ProductOver, [fx;var;start; stop]) -> Some(fx,var,start, stop) 
    | _ -> None

///(fx, var)
let (|ProductsVar|_|) input =
    match input with
    | FunctionN(ProductOver, [fx;var]) -> Some(fx,var) 
    | FunctionN(ProductOver, [fx;var;_; _]) -> Some(fx,var)
    | _ -> None

///(fx)
let (|ProductsTerm|_|) input =
    match input with
    | FunctionN(ProductOver, [fx]) -> Some(fx) 
    | FunctionN(ProductOver, [fx;_;_;_]) -> Some(fx)
    | FunctionN(ProductOver, [fx;_]) -> Some(fx)
    | _ -> None

let (|IsIndexed|_|) input =
    match input with 
    | FunctionN(Indexed, w::_) -> Some w 
    | _ -> None

//active pattern for superposition principle
let (|IsLinearFn|_|) input =
    match input with
    | IsTotalDerivative(e, dx) -> Some(e, diff dx)
    | IsPartialDerivative(e, dx) -> Some(e, pdiff dx) 
    | IsIntegral(e, dx) -> Some(e, integral dx)
    | Summation(fx, var, start, stop) -> Some(fx, fun x -> summation x var start stop)
    | Sum l as sums -> Some(sums, id)
    | _ -> None

let (|IsSealed|_|) input =
    match input with
    | Id(x,_) -> Some(x)
    | _ -> None

//========================
  
//checks if is derivative or nth derivative already, if nth make nth+1, if not wrap, if derivative make nth

/// <summary>
/// Generalizes derivative operations by handling nested derivatives and combining them.
/// </summary>
/// <param name="D">The derivative operation function (either diff or pdiff)</param>
/// <param name="expr">The expression to differentiate</param>
/// <returns>The simplified derivative expression</returns>
/// <remarks>
/// This function handles three cases:
/// 1. Simple derivatives: Applies the derivative operation directly
/// 2. Nested derivatives with same variable: Combines into nth derivative
/// 3. Nth derivatives with same variable: Increments the order
/// 
/// Examples:
/// - d/dx(d/dx(f)) -> d²f/dx²
/// - d/dx(d²f/dx²) -> d³f/dx³
/// - ∂/∂x(∂f/∂x) -> ∂²f/∂x²
/// </remarks>
let gdiffn1 D expr =
    match D expr with 
    | IsDerivative(_, _, dxOuter) ->  
        match expr with
        | IsDerivative(fn, f, dx) when dx = dxOuter ->
            match fn with 
            | Derivative -> diffnth 2 dx f
            | PartialDerivative -> pdiffnth 2 dx f
            | _ -> D expr 
        | IsNthDerivative(fn, f, dx, n) when dx = dxOuter ->
            match fn with 
            | Derivative -> diffnth (n+1) dx f
            | PartialDerivative -> pdiffnth (n+1) dx f
            | _ -> D expr
        | _ -> D expr
    | _ -> D expr

let pdiffn dx x = gdiffn1 (pdiff dx) x
let diffn dx x = gdiffn1 (diff dx) x
//==============

type Summations() =
    //sigma symbol
    static member Σ(var, start, stop, fx) = summation var start stop fx
    static member Σ(var, fx) = FunctionN(SumOver, [fx;var])

module Prob =
    let expectationsDistribution = function
        | IsExpectation (_, px) -> px
        | _ -> Undefined

    let expectationsInnerProb = function
        | IsExpectation (_, IsProb (_, x)) -> x
        | _ -> Undefined

    let inner = function
        | IsProb (_, x) -> x
        | _ -> Undefined

    let isProb = function | IsProb _ -> true | _ -> false

    let isExpectation = function IsExpectation _ -> true | _ -> false  

    let getVariable = 
        let getinner = function 
            | IsProb(_, x) -> Some x
            | IsCondProb(_, x, Tupled l) -> Some (tuple (List.distinct (x :: l)))
            | IsCondProb(_, Tupled l, x) -> Some (tuple (List.distinct (l @ [x])))
            | IsCondProb(_, Tupled l, Tupled l') -> Some (tuple (List.distinct (l @ l')))
            | IsCondProb(_, x, theta) -> Some (tuple (List.distinct [x; theta]))
            | _ -> None
        function 
        | Definition(px, _, _) -> getinner px
        | px -> getinner px

    let getVariableConditional =  
        let getinner = function 
            | IsCondProb(_, x,y) -> Some (x,y)
            | _ -> None
        function 
        | Definition(px, _, _) -> getinner px
        | px -> getinner px      


    //P(A|B) = P(A∩B)/P(B)
    let condToJoint = function
        | IsCondProb(n, x, theta) ->
            probn n (tuple [x; theta]) / probn n theta
        | IsCondProb(n, Tupled l, theta) ->
            probn n (tuple (l @ [theta])) / probn n theta
        | IsCondProb(n, x, Tupled l) ->
            probn n (tuple (x :: l)) / probn n (tuple l) 
        | IsCondProb(n, Tupled l, Tupled l') ->
            probn n (tuple (l @ l')) / probn n (tuple l')
        | _ -> Undefined


//////////

let toLatexTableString colheaders (t: string[][]) =
    let colhtext =
        colheaders
        |> List.map (fun s -> "\\text{ " + s + " }")
        |> String.concat " & "

    let colformat = Array.replicate (t[0].Length) "c"

    let header =
        $"""\begin{{array}}{{|{String.concat "|" colformat}}}"""
        + "\n"

    let format =
        t
        |> Array.map (String.concat " & ")
        |> String.concat "\\\\\n"

    let footer = "\n\\end{array}"

    header
    + colhtext
    + "\\\\\n\hline\n"
    + format
    + footer


let fmttext (s: string) = 
    if expressionFormat = LatexFormat then $"\\text{{{s}}}"
    else s



