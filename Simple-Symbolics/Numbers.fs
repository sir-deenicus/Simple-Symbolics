﻿module MathNet.Symbolics.NumberTheory

open MathNet.Numerics
open MathNet
open MathNet.Symbolics.Utils
open System

module BigRational =
    open Microsoft.FSharp.Core.Operators
    open System

    let almostZero x = (floor x) / x > 0.999999

    let fromFloatDouble (df : float) =
        let rec countDigits n x =
            let x' = x * 10.
            if almostZero x' then n + 1
            else countDigits (n + 1) x'
        if almostZero df then BigRational.FromBigInt(Numerics.BigInteger df)
        else
            let dpart = df - floor df
            let dpow = countDigits 0 dpart
            let pow10 = Numerics.BigInteger 10 ** int dpow
            BigRational.FromBigIntFraction
                (Numerics.BigInteger(df * double pow10), pow10)

    ///limited by range of decimal (which is used as a less noisy alternative to floats)
    let fromFloat (f : float) =
        let df = decimal f
        if df = floor df then BigRational.FromBigInt(Numerics.BigInteger df)
        else
            let decimalpart = string (df - floor df)
            let pow10 = Numerics.BigInteger 10 ** (decimalpart.Length - 2)
            BigRational.FromBigIntFraction
                (Numerics.BigInteger(df * decimal pow10), pow10)

    let fromFloatRepeating (f : float) =
        let df = decimal f
        let len = float ((string (df - floor df)).Length - 2)
        let pow10 = decimal (10. ** len)
        if abs f < 1. then
            BigRational.FromIntFraction
                (int (df * pow10), int (floor (pow10 - df)))
        else
            BigRational.FromIntFraction
                (int (df * pow10 - floor df), int (pow10 - 1M))

type Expression with
    member t.ToFormattedString() = expressionFormater t
    member t.ToFloat() = (Evaluate.evaluate (Map.empty) t).RealValue
    member t.ToComplex() = (Evaluate.evaluate (Map.empty) t).ComplexValue 

    member t.ToInt() =
        match t with
        | Number n -> int n
        | _ -> failwith "not a number"

    member t.ToRational() =
        match t with
        | Number n -> Some n
        | _ -> None

module Expression = 
    open MathNet.Symbolics
    open System

    let fromFloatDouble f =
        BigRational.fromFloatDouble f |> Expression.FromRational
    let fromFloat f = BigRational.fromFloat f |> Expression.FromRational
    let fromFloatRepeating f =
        BigRational.fromFloatRepeating f |> Expression.FromRational
    let toFloat (x : Expression) = x.ToFloat()
    let toInt (i : Expression) = i.ToInt()
    let toRational (i : Expression) = i.ToRational()
    let toPlainString = Infix.format
    let toFormattedString (e : Expression) = e.ToFormattedString()
    let toSciNumString r (x : float) =
        let npow =
            if x > 0. then Some(floor (log10 x))
            elif x < 0. then Some(floor (log10 -x))
            else None
        match npow with
        | Some n when n < -4. || n > 6. ->
            let pow10 = Power(10Q, Expression.FromInt32(int n))
            let num = Math.Round(x / (10. ** n), 2)
            let prefix = if abs num = 1. then sprintf "%s" (signstr num) else sprintf "%s × " (num.ToString("N2"))
            sprintf "%s%s" prefix
                (pow10.ToFormattedString())
        | _ ->
            if r > 6 then string x
            else x.ToString("N" + string r) 

    let isRationalNumber =
        function
        | Number _ -> true
        | _ -> false

    let isNumber =
        function
        | Number _ | Constant _ | Approximation _
        | Power(Number _, Number _)  
        | Power(Approximation _, Number _)  
        | Power(Constant _, Number _)  
        | Power(Number _, Constant _)
        | Power(Constant _, Constant _) 
        | Product [ Number _; Constant _ ] ->
            true
        | _ -> false
        
    let isInteger =
        function
        | Number n when n.IsInteger -> true
        | _ -> false 

    let isNegativeOrZeroNumber n =
        if isNumber n then
            n.ToFloat() <= 0.
        else false

    let isNegativeNumber n =
        if isNumber n then
            n.ToFloat() < 0.
        else false

    let hasNegatives = function
        | Product (Number n::_) -> n < 0N
        | x -> isNegativeNumber x 

    let isPositiveNumber n =
        if isNumber n then
            n.ToFloat() >= 0.
        else false

    let rec isPositiveExpressionRec = function
        | Function(Abs,_) -> true
        | Power(_,Number n) when (int n)%2 = 0 -> true
        | Sum l
        | Product l -> List.forall isPositiveExpressionRec l
        | x -> isPositiveNumber x

    let isPositiveExpression = function
        | Product l
        | Sum l -> List.forall isPositiveExpressionRec l
        | x -> isPositiveExpressionRec x 

let (|ProductHasNumber|_|) =
    function
    | Product l ->
        match l |> List.filter (Expression.isRationalNumber) with
        | [ Number n ] -> Some(Expression.FromRational n)
        | _ -> None
    | _ -> None 

let (|RationalLiteral|_|) r = function
    | Number n as q when n = BigRational.FromIntFraction r -> Some q
    | _ -> None

let (|IntegerLiteral|_|) m = function
    | Number n as q when n.IsInteger && int n = m -> Some q
    | _ -> None

let (|IntegerNumber|_|)  = function
    | Number n as q when n.IsInteger -> Some q
    | _ -> None

let (|IsNumber|_|) = function
      | e when Expression.isNumber e -> Some e
      | _ -> None
   
let productToConstantsAndVarsGen test =
    function
    | Number _ as n when test n -> Some(n, [])
    | Product p ->
        let nums, vars = List.partition test p
        Some(List.fold (*) 1Q nums, vars)
    | _ -> None

let productToConstantsAndVars = productToConstantsAndVarsGen Expression.isNumber

let productToIntConstantsAndVars =
    productToConstantsAndVarsGen Expression.isInteger

let inline rem n d =
    let rec loop n = if n >= d then loop (n-d) else n
    loop n   

let rec gcd c d = 
    match (abs c,abs d) with
    | (a, n) when n = 0N -> a
    | (a,b) -> gcd b (rem a b) 

let rec factorial (n : BigRational) =
    if n <= 1N then 1N
    else n * factorial (n - 1N)

let rec factorialSymbolic (e : Expression) =
    match e with 
    | Number m when m < 15N -> Number(factorial m)
    | _ -> failwith "Must be a number < 15"

let inline primefactors factor x =
    let rec loop x =
        match factor x with
        | [ one ] -> [ one ]
        | [ x; _ ] -> [ x ]
        | _ :: (nextfactor :: _) -> //first number is the largest, = input
            let r = x / nextfactor
            let f1, f2 = loop r, loop nextfactor
            f1 @ f2
        | _ -> failwith "unexpected error"
    loop x

let inline factors toint f x =
    let x' = toint x
    let sqrtx = int (sqrt (float x'))
    [ for n in 1..sqrtx do
          let m = x' / n
          if x' % n = 0 then
              yield f n
              if m <> n then yield f m ]
    |> List.sortByDescending toint

let factorsExpr = abs >> factors Expression.toInt Expression.FromInt32

let groupPowers singletonLift pl =
    List.groupBy id pl
    |> List.map (fun (x, l) ->
           if l.Length = 1 then singletonLift x
           else Power(x, Expression.FromInt32(List.length l)))

let primefactorsPartial x =
    match productToIntConstantsAndVars x with
    | Some(ns, vs) -> Some(vs @ primefactors factorsExpr (abs ns), ns)
    | None -> None

let rec partitions =
    function
    | 0 -> []
    | n ->
        let k = [ 1 ] :: partitions (n - 1)
        [ for p in k do
              yield [ 1 ] @ p
              if p.Length < 2 || p.Tail.Head > p.Head then
                  yield [ p.Head + 1 ] @ p.Tail ]
        |> List.filter (List.sum >> (=) n)

let primeFactorsExpr =
    abs
    >> primefactors factorsExpr
    >> groupPowers (fun x -> Sum [ x ])
    >> Product

let primeFactorsPartialExpr =
    primefactorsPartial
    >> Option.map (fst
                   >> groupPowers (fun x -> Sum [ x ])
                   >> Product) 

let chooseN n k = 
    if k < n then 0Q
    else
        let bn, bk = BigRational.FromInt n, BigRational.FromInt k
        if k = 0 || n = k then 1Q 
        else
            factorial bn / (factorial bk * (factorial (bn - bk))) 
            |> Expression.FromRational
    
let fac x = Function(Fac, x)

let expandChooseBinomial = function
    | Binomial(n,k) -> fac n /(fac k * fac(n - k))
    | x -> x

let sterlingsApproximation = function
    | Function(Fac, x) ->
        sqrt(2Q * Operators.pi * x) * (x/Constants.e)**x
    | x -> x

let approximateFactorial = function Function(Fac,x) -> (x/(Constants.e))**x | x -> x
 
let rational x = Expression.fromFloat x

let tryNumber =
    function
    | Number n -> Some(float n)
    | IsNumber n -> Some(n.ToFloat())
    | PositiveInfinity -> Some(Double.PositiveInfinity)
    | NegativeInfinity -> Some(Double.NegativeInfinity)
    | x ->
        try
            Some(Expression.toFloat x)
        with _ -> None
    | _ -> None