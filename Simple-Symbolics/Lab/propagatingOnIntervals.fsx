
#load @"C:\Users\cybernetic\Jupyter-Notebooks\maths-repl.fsx"

open MathNet.Numerics
open Prelude.Common
open System
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Operators
open MathNet.Symbolics.Utils 
open MathNet.Symbolics.Differentiation 
open MathNet.Symbolics.LinearAlgebra
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Summation
open MathNet.Symbolics.Units
open MathNet.Symbolics.NumberTheory
open Expression


// In certain cases, it is useful to propagate information of what restrictions are placed on domain and ranges as functions are composed. To get some insights on this, I'll be investigating cos, arccos, sqrt and log.

//For a start, it is useful to have a way to represent domains and ranges and attach them to an expression or a function. A variable has a domain that is just itself. These can then be composed together.

[<RequireQualifiedAccess>]
type ApplyAble =
    | Sqrt
    | Log
    | Exp
    | Cos
    | ArcCos

type VarType =
    | Var of Expression
    | Application of ApplyAble

let getVar =
    function
    | Var x -> x
    | _ -> failwith "Not Var"

let getFunc = function
    | Application f -> f
    | _ -> failwith "error"

let fapply x =
    function
    | ApplyAble.Sqrt -> sqrt x
    | ApplyAble.Exp -> exp x
    | ApplyAble.Log -> ln x
    | ApplyAble.Cos -> cos x
    | ApplyAble.ArcCos -> arccos x

//The task is to get the range (output of one function) to agree with the domain (input of the other) by taking the intersection from their overlap.

let align (range1, range2) (domain1, domain2) =
    match (tryNumber range1, tryNumber range2),
          (tryNumber domain1, tryNumber domain2) with
    | (Some r1, Some r2), (Some d1, Some d2) -> //What is overlap?
        if r1 >= d1 && r2 <= d2 then (range1, range2) //is (r1,r2) inside? eg (3, 4) (2,5)-> (3,4)
        elif r1 <= d1 && r2 >= d1 && r2 <= d2 then (domain1, range2) // r1--d1--r2--d2? (1,3) (2,5)-> (2,3)
        elif r1 >= d1 && r1 <= d2 && r2 >= d2 then (range1, domain2) //d1--r1--d2--r2
        elif r1 <= d1 && r2 >= d2 then (domain1, domain2) //(d1,d2) is contained in (r1,r2)
        else failwith "No intersection"
    | _ -> failwith "No intersection"

let deduceRange =
    function
    | (ApplyAble.Log, (Number n, Number m), _) when n >= 0N && m <= 1N ->
        -infinity, 0Q
    | (f, (Number _ as n, (Number _ as m)), _) -> fapply n f, fapply m f
    | (f, (n,m), _) when Expression.isNumber n && isNumber m -> fapply n f, fapply m f
    | (_, _, r) -> r

let applyRange =
    function
    | (f, (n, m)) ->
        fapply n f |> Expression.FullSimplify,
        fapply m f |> Expression.FullSimplify

type Composer =
    { Domain : Expression * Expression
      Range : Expression * Expression
      Expr : VarType
      Depth : int
      Input : Composer option }

    static member New(x) =
        { Range = -infinity, infinity
          Domain = x, x
          Expr = Var x
          Depth = 0
          Input = None }

    static member New(range, x) =
        { Range = range
          Domain = x, x
          Expr = Var x
          Depth = 0
          Input = None }

    static member New(domain, range, f) =
        { Range = range
          Domain = domain
          Expr = Application f
          Depth = 0
          Input = None }

    member r.ToExpr() =
        match r.Expr with
        | Application f ->
            match r.Input with
            | None -> failwith "construction error"
            | Some v -> fapply (v.ToExpr()) f
        | Var x -> x

    member r.Apply(x : Composer) =
        let f = getFunc r.Expr
        let domain' = align x.Range r.Domain
        { Range = deduceRange (f, domain', r.Range)
          Input = Some x
          Domain = domain'
          Depth = x.Depth + 1
          Expr = Application(f) }

    //After the function has worked out domains from a forward pass, a backwards pass then needs to work out--to then work backwards to adjust the domains and ranges at each level of iteration/application below root to be correct with respect to the one above. This involves solving for x in a simple dummy equation of f(x) = r where f is the applied function. The allowable range of the final input to the function can be worked out in this way.
    member r.Align() =
        let rec downprop inputrange (composed : Composer) =
            match composed.Input with
            | Some(input) ->
                match input.Expr with
                | Var x ->
                    let (r1, r2) = defaultArg inputrange input.Range
                    let expr = composed.ToExpr()
                    let r1' =
                        (expr <=> r1 |> Solving.reArrangeEquation x).Right
                        |> Expression.FullerSimplify
                    let r2' =
                        (expr <=> r2 |> Solving.reArrangeEquation x).Right
                        |> Expression.FullerSimplify
                    { composed with Range = (r1, r2)
                                    Domain = (r1', r2')
                                    Input = Some { input with Range = (r1', r2') } }
                | _ ->
                    let f = getFunc composed.Expr

                    let (r1', r2') as domain' =
                        match inputrange with
                        | None -> composed.Domain
                        | Some(r1, r2) ->
                            let fexpr = fapply x f
                            (fexpr <=> r1 |> Solving.reArrangeEquation x).Right
                            |> Expression.FullerSimplify,
                            (fexpr <=> r2 |> Solving.reArrangeEquation x).Right
                            |> Expression.FullerSimplify

                    let modifiedinput = downprop (Some(r1', r2')) input
                    { composed with Domain = domain'
                                    Range = applyRange (f, domain')
                                    Input = Some modifiedinput }
            | None -> failwith "unreachable"
        if r.Depth = 1 then
            match r.Expr, r.Input with
            | VarType.Application f, Some i -> 
                {r with Range = applyRange (f, i.Range)}
            | _ -> r            
        else downprop None r


let rsqrt = Composer.New((0Q, infinity), (0Q, infinity), ApplyAble.Sqrt)
let logx = Composer.New((0Q, infinity), (-infinity, infinity),ApplyAble.Log)
let cosx = Composer.New((-infinity, infinity), (-1Q, 1Q), ApplyAble.Cos)
let arccosx = Composer.New((-1Q, 1Q), (-pi/2, pi/2), ApplyAble.ArcCos)
let expx = Composer.New((-infinity, infinity), (0Q, infinity),ApplyAble.Exp)


let x1 = Composer.New(x)
let x2 = Composer.New((0Q,1Q), x)

expx.Apply(Composer.New((-infinity,0Q), x)).Align()

logx.Apply x2

(cosx.Apply x2).Range |> snd |> Expression.FullerSimplify

logx.Apply(cosx.Apply x2)

logx.Apply(cosx.Apply x2).Align()

arccosx.Apply(Composer.New((Constants.e,Constants.e),Constants.e))

let zz = rsqrt.Apply(logx.Apply(cosx.Apply x1))
zz
zz.Align()
zz.ToExpr() |> replaceSymbol 0Q x |> Expression.toFloat


type Comparer = Gt | Lt | Gte | Lte | Eq

type Boundary = Open | Closed 
type IntervalType = (Boundary * Expression)

type IntervalExpr(lower:IntervalType, upper : IntervalType) =
    let mutable lowerval = lower
    let mutable upperval = upper

    let minx a b =
        match tryNumber (snd a), tryNumber (snd b) with 
        | Some x, Some y -> if x < y then a else b
        | _ -> a
 

    member __.Lower = lowerval
    member __.Upper = upperval
    member __.SetInterval(a,b) = lowerval <- a; upperval <- b
    new() = IntervalExpr((Closed, -infinity), (Closed, infinity))
    new(a) = IntervalExpr((Closed, Expression.FromRational a), (Closed, Expression.FromRational a))
    new((a,b)) = 
        let a' = min a b
        let b' = max a b 
        IntervalExpr((Closed, Expression.FromRational a'), (Closed, Expression.FromRational b'))
    new(a,b) = IntervalExpr((Closed,a), (Closed,b))
    member __.IsLessThanOrEqualTo(y:IntervalExpr) = 
        lowerval <- minx lowerval y.Lower
        upperval <- minx upperval y.Upper
    static member (-) (a:IntervalExpr,b:IntervalExpr) =
        let minus infinitycase x y =
            match x, y with   
            | x, y when x = y && isInfinity x -> infinitycase
            | x,y -> x - y
        IntervalExpr(minus -infinity (snd a.Lower) (snd b.Lower), minus 0Q(snd a.Upper) (snd b.Upper))

let xi = IntervalExpr() //< IntervalExpr()
let yi = IntervalExpr()
yi.IsLessThanOrEqualTo(xi)
yi - xi

-10 - -10

//Such variables should communicate with each other and propagate changes.
type ComparableExpression(x:Expression, lower: Expression, upper : Expression) =
   let vars = Dict()
   do
       if lower = upper then vars.Add(lower, Eq)
       else
           match tryNumber lower with
           | None -> vars.Add(lower, Gte)
           | _ -> ()

           match tryNumber upper with
           | None -> vars.Add(upper, Lte)
           | _ -> ()
   new(e) = ComparableExpression(e,e,e)
   member __.Vars = vars
   member __.Expression = x
   member __.Lower = lower
   member __.Upper = upper

   member x.SetAs(comparer:Comparer, y:Expression) =
       vars.Add(y, comparer)
   interface IComparable with
           member this.CompareTo(thatObj) =
               match thatObj with
               | :? ComparableExpression as that ->
                   match (tryNumber this.Lower, tryNumber this.Upper), (tryNumber that.Lower, tryNumber that.Upper) with
                   | (Some l1,Some u1), (Some l2, Some u2) ->
                       if l1 > u2 then 1
                       elif u1 < l2 then -1
                       elif l1 < l2 && u1 <= u2 then -1
                       elif l1 >= l2 && u1 > u2 then 1
                       elif l1 = l2 && u1 = u2 then 0
                       else failwith "Not comparable"
                   | _ -> failwith "Not comparable"
               | _ ->
                   raise <| ArgumentException("Can't compare instances of different types")

ComparableExpression(x)

ComparableExpression(x,4Q, 8Q) > ComparableExpression(y, 4Q, 7Q)
