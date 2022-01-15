﻿module MathNet.Symbolics.Equations

open MathNet.Symbolics
open MathNet.Symbolics.Utils
open Prelude.Common
open NumberProperties

type Equation(leq : Expression, req : Expression) =
    member __.Definition = leq, req
    member __.Left = leq
    member __.Right = req
    member __.Equalities =
        [ leq, req
          req, leq ]
    
    static member ApplyToRight f (eq:Equation) = 
        let leq, req = eq.Definition
        Equation(leq, f req)
    static member ApplyToLeft f (eq:Equation) = 
        let leq, req = eq.Definition
        Equation(f leq, req)
    static member Apply f (eq:Equation) = 
        let leq, req = eq.Definition
        Equation(f leq, f req)
    static member (-) (eq : Equation, expr : Expression) =
        Equation(eq.Left - expr, eq.Right - expr)
    static member (+) (eq : Equation, expr : Expression) =
        Equation(eq.Left + expr, eq.Right + expr)
    static member (*) (eq : Equation, expr : Expression) =
        Equation(eq.Left * expr, eq.Right * expr)
    static member (/) (eq : Equation, expr : Expression) =
        Equation(eq.Left / expr, eq.Right / expr)
    static member Pow(e:Equation, n : Expression) = 
        Equation (e.Left ** n, e.Right ** n)
    static member Pow(e:Equation, n : int) = 
        Equation (e.Left ** n, e.Right ** n)
    override __.ToString() =
        fmt leq + " = " + fmt req
    override e.Equals(o:obj) =
        match o with 
        | :? Equation as e2 -> e.Definition = e2.Definition
        | _ -> false

    override e.GetHashCode() = e.Definition.GetHashCode()

    interface System.IEquatable<Equation> with
        member this.Equals(that : Equation) = this.Definition = that.Definition
 
 type InEquation(leq : Expression, req : Expression) =
     member __.Definition = leq, req
     member __.Left = leq
     member __.Right = req 
      
     static member (-) (eq : InEquation, expr : Expression) =
         InEquation(eq.Left - expr, eq.Right - expr)
     static member (+) (eq : InEquation, expr : Expression) =
         InEquation(eq.Left + expr, eq.Right + expr)
     static member (*) (eq : InEquation, expr : Expression) =
         InEquation(eq.Left * expr, eq.Right * expr)
     static member (/) (eq : InEquation, expr : Expression) =
         InEquation(eq.Left / expr, eq.Right / expr)
     static member Pow(e:InEquation, n : Expression) = 
         InEquation (e.Left ** n, e.Right ** n)
     static member Pow(e:InEquation, n : int) = 
         InEquation (e.Left ** n, e.Right ** n)
     override __.ToString() =
         let symbol = if expressionFormat = LatexFormat then " \\neq " else " ≠ "
         fmt leq + symbol + fmt req 
 
     
module Equation =
    let swap (eq:Equation) = Equation(swap eq.Definition) 
    let right (eq:Equation) = eq.Right
    let left (eq:Equation) = eq.Left
    
    ///convenience function that multiplies by denominator of right and left sides of equation and then subtracts right side ex : a/b = c /d -> a * d = b * c -> a * d - b * c = 0
    let multiplyDenominatorsAndSubtract (e:Equation) =
        let e' = e * Rational.denominator e.Right * Rational.denominator e.Left
        e' - e'.Right 

    let subtractRHS (e:Equation) = e - e.Right 


let (<=>) a b = Equation(a, b)

let (=/=) a b = InEquation(a,b)   

let equals a b = Equation(a, b)

let oEqapply = Equation.Apply >> Op

let iEqapply (s,f) = Instr(Equation.Apply f, s)
  
let equationTrace (current:Equation) (instructions : _ list) = 
    stepTracer false true string current instructions

let eqApp = Equation.Apply
 
//============== 

module InEquality =
    type Comparer =
        | Lesser
        | Greater
        | Geq
        | Leq
        override t.ToString() =
            match t with
            | Lesser -> "<"
            | Greater -> ">"
            | Leq ->
                match expressionFormat with
                | InfixFormat -> " ≤ "
                | _ -> " \\leq "
            | Geq ->
                match expressionFormat with
                | InfixFormat -> " ≥ "
                | _ -> " \\geq "

    let flipComparer =
        function
        | Lesser -> Greater
        | Greater -> Lesser
        | Leq -> Geq
        | Geq -> Leq

    type NumSign =
        | Positive
        | Negative
        | Nil


type InEquality(comparer: InEquality.Comparer,
                leq: Expression,
                req: Expression,
                ?existingConditions: InEquality seq,
                ?existingSigns) =

    let conditions =
        defaultArg
            (Option.map (fun (h : seq<InEquality>) -> Hashset(h))
                 existingConditions) (Hashset<InEquality>())

    let varsigns =
        defaultArg existingSigns (Dict<Expression, InEquality.NumSign>())

    member __.Definition = leq, comparer, req
    member __.Left = leq
    member __.Right = req
    member __.Comparer = comparer
    member __.VarSigns = varsigns
    member __.Conditions = Seq.toArray conditions

    member __.GetSign =
        match req with //is positive
        | Function (Abs, _) ->
            match comparer with
            | InEquality.Geq
            | InEquality.Greater -> Some(InEquality.Positive)
            | _ -> None
        | IsRealNumber n ->
            let isNegativeOrZero = Expression.isNegativeOrZeroNumber n

            if isNegativeOrZero then
                let num = n.ToFloat().Value

                match comparer with
                | InEquality.Leq when num < 0. -> Some(InEquality.Negative)
                | InEquality.Lesser -> Some(InEquality.Negative)
                | InEquality.Geq
                | InEquality.Greater when num = 0. -> Some(InEquality.Positive)
                | _ -> None
            else
                match comparer with //is positive
                | InEquality.Geq
                | InEquality.Greater -> Some(InEquality.Positive)
                | _ -> None
        | _ -> None

    override __.ToString() =
        leq.ToFormattedString()
        + string comparer
        + req.ToFormattedString()
        + newline ()
        + (Seq.map string conditions
           |> String.concat (newline ()))

    member i.Flip() =
        i.OfExpr(InEquality.flipComparer comparer, req, leq)

    member i.ApplyToRight f = i.OfExpr(i.Left, f i.Right)

    member i.ApplyToLeft f = i.OfExpr(f i.Left, i.Right)

    member i.Apply f = i.OfExpr(f i.Left, f i.Right)

    static member applyToRight f (e: InEquality) = e.ApplyToRight f

    static member applyToLeft f (e: InEquality) = e.ApplyToLeft f

    static member apply f (e: InEquality) = e.Apply f

    member i.AddCondition(c: InEquality) =
        match c.Left with
        | Identifier _ as x ->
            match c.GetSign with
            | None -> ()
            | Some s -> varsigns.Add(x, s)
        | _ -> ()

        conditions.Add c |> ignore
        i

    static member decideComparison(eq: InEquality, expr: Expression) =
        let isnum = Expression.isNumber expr

        let c, safe =
            match Expression.isNegativeNumber expr, eq.VarSigns.tryFind expr with
            | false, Some InEquality.Negative
            | true, _ -> InEquality.flipComparer eq.Comparer, true
            | false, Some InEquality.Positive
            | _ when isnum -> eq.Comparer, true
            | _ -> eq.Comparer, false

        let cond =
            if not safe
            then Some(InEquality(InEquality.Comparer.Greater, expr, 0Q))
            else None

        c, cond

    member eq.OfExpr(l, r) =
        InEquality(eq.Comparer, l, r, eq.Conditions, eq.VarSigns)

    member eq.OfExpr(comparer, l, r) =
        InEquality(comparer, l, r, eq.Conditions, eq.VarSigns)

    static member (*)(eq: InEquality, expr: Expression) =
        let comparer, cond = InEquality.decideComparison (eq, expr)

        let ineq =
            eq.OfExpr(comparer, eq.Left * expr, eq.Right * expr)

        match cond with
        | None -> ineq
        | Some c -> ineq.AddCondition c

    static member (+)(eq: InEquality, expr: Expression) =
        eq.OfExpr(eq.Left + expr, eq.Right + expr)

    static member (-)(eq: InEquality, expr: Expression) =
        eq.OfExpr(eq.Left - expr, eq.Right - expr)

    static member (/)(eq: InEquality, expr: Expression) =
        let comparer, cond = InEquality.decideComparison (eq, expr)

        let ineq =
            eq.OfExpr(comparer, eq.Left / expr, eq.Right / expr)

        match cond with
        | None -> ineq
        | Some c -> ineq.AddCondition c 

let leq a b = InEquality(InEquality.Comparer.Leq,a,b)
let geq a b = InEquality(InEquality.Comparer.Geq,a,b)
let lt a b = InEquality(InEquality.Comparer.Lesser,a,b)
let gt a b = InEquality(InEquality.Comparer.Greater,a,b) 
 

let inEqualityTrace (current:InEquality) (instructions : _ list) = 
    stepTracer false true string current instructions
      