// #load @"C:\Users\cybernetic\Jupyter-Notebooks\maths.fsx"
//
// open XPlot.Plotly
// open Maths
// open MathNet.Symbolics.Differentiation
// open MathNet.Numerics
// open Prelude.Common
// open System
// open MathNet.Symbolics.Core
// open MathNet.Symbolics
// open MathNet.Symbolics.Core.Vars
// open MathNet.Symbolics.Operators
// open MathNet.Symbolics.Utils
// open MathNet.Symbolics.Differentiation
// open MathNet.Symbolics.LinearAlgebra
// open MathNet.Symbolics.Solving
// open MathNet.Symbolics.Units
// open NumberProperties
// open Expression
// open Equations
// open Trigonometry
// open MathNet.Symbolics.Currencies.Units
// open Integration
// open FunctionHelpers
// open FSharp.Data
// open Hansei.Backtracking
// open Prelude.Math
// open Hansei.Continuation
// open Hansei.FSharpx.Collections
//
// #time "on"

setLatex()

let ab = a + b

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
