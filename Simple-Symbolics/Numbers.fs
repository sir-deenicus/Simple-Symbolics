module MathNet.Symbolics.NumberTheory

open MathNet.Numerics
open MathNet
open MathNet.Symbolics.Utils
open System
         
let (|RealConstant|_|) =
    function
    | Constant Constant.I -> None
    | Constant c -> Some c
    | _ -> None

let (|RealApproximation|_|) =
    function 
    | Approximation (Approximation.Real r) -> Some r
    | _ -> None

let (|AsInteger|_|) = function
    | Number n when n.IsInteger -> Some n.Numerator
    | _ -> None

module BigRational =
    open Microsoft.FSharp.Core.Operators
    open System

    let approximatelyInt x = 
        let ratio = (floor x) / x 
        ratio > 0.999999 && ratio < 1.000001

    let fromFloatDouble (df : float) =
        let rec countDigits n x =
            let x' = x * 10.
            if approximatelyInt x' then n + 1
            else countDigits (n + 1) x'
        if approximatelyInt df then BigRational.FromBigInt(Numerics.BigInteger df)
        else
            let df' = abs df
            let dpart = df' - floor df'
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
    member t.ToFloat() = try Some (Evaluate.evaluate (Map.empty) t).RealValue with _ -> None
    member t.ToComplex() = (Evaluate.evaluate (Map.empty) t).ComplexValue 
    member t.ToBigInt() = 
        match t with
        | AsInteger n -> n
        | _ -> failwith "not an integer"

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
    let toBigInt(i:Expression) = i.ToBigInt()
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
        | Power(Number _, Approximation _) 
        | Power(Approximation _, Number _)  
        | Power(Constant _, Number _)  
        | Power(Number _, Constant _)
        | Power(Constant _, Constant _) 
        | Product [ Number _; Constant _ ] ->
            true
        | _ -> false 

    let isRealNumber =
        function
        | Number _ | RealConstant _ | RealApproximation _
        | Power(Number _, Number _)  
        | Power(Number _, RealApproximation _) 
        | Power(RealApproximation _, Number _)  
        | Power(RealConstant _, Number _)  
        | Power(Number _, RealConstant _)
        | Power(RealConstant _, RealConstant _) 
        | Product [ Number _; RealConstant _ ] ->
            true
        | _ -> false       

    let isInteger =
        function
        | Number n when n.IsInteger -> true
        | _ -> false 

    let isNegativeOrZeroNumber n =
        if isNumber n then
            match n.ToFloat() with 
            | Some x -> x <= 0. 
            | None -> false
        else false

    let isNegativeNumber n =
        if isNumber n then
            match n.ToFloat() with 
            | Some x -> x < 0. 
            | None -> false 
        else false

    let hasNegative = function
        | Product (Number n::_) -> n < 0N
        | x -> isNegativeNumber x 

    let isPositiveNumber n =
        if isNumber n then 
            match n.ToFloat() with 
            | Some x -> x >= 0. 
            | None -> false
        else false

    let rec isPositiveExpression = function
        | Function(Abs,_) -> true
        | Power(_,Number n) when (int n)%2 = 0 -> true
        | Sum l
        | Product l -> List.forall isPositiveExpression l
        | x -> isPositiveNumber x 

module Structure = 
    let productToConstantsAndVarsAux test =
        function
        | Number _ as n when test n -> Some(n, [])
        | Product p ->
            let nums, vars = List.partition test p
            Some(List.fold (*) 1Q nums, vars)
        | _ -> None

    let productToConstantsAndVars = productToConstantsAndVarsAux Expression.isNumber

    let productToIntConstantsAndVars =
        productToConstantsAndVarsAux Expression.isInteger
          
///////////////////////////////////////////////

let (|ProductHasNumber|_|) =
    function
    | Product l ->
        match l |> List.filter (Expression.isRationalNumber) with
        | [ Number n ] -> Some(Expression.FromRational n)
        | _ -> None
    | _ -> None 

let (|Fraction|_|) = function 
    | Number n when n.Denominator <> 1I -> Some((n.Numerator, n.Denominator))
    | _ -> None 

let (|RationalLiteral|_|) r = function
    | Number n as q when n = BigRational.FromIntFraction r -> Some q
    | _ -> None

let (|IntegerLiteral|_|) m = function
    | Number n as q when n.IsInteger && int n = m -> Some q
    | _ -> None

let (|IntegerNumber|_|) = function
    | Number n as q when n.IsInteger -> Some q
    | _ -> None 

let (|IsNumber|_|) = function
      | e when Expression.isNumber e -> Some e
      | _ -> None

let (|IsRealNumber|_|) = function
      | e when Expression.isRealNumber e -> Some e
      | _ -> None
       
let (|IsFloatingPoint|_|) = function
    | IsRealNumber n -> n.ToFloat()
    | _ -> None
     
let (|SquareRoot|_|) = function
      | Power(e, n) when n = 1Q/2Q -> Some e
      | _ -> None
   
let (|IsNegativeNumber|_|) = function
      | e when Expression.isNegativeNumber e -> Some e
      | _ -> None 

let (|Minus|_|) = function
      | Sum [Product [Number n; a]; b]
      | Sum [a; Product [Number n; b]] when n = -1N -> Some (a,b)
      | Sum [Number n; a] when n < 0N -> Some(Number n, a)
      | _ -> None  
       
let (|Divide|_|) e =
    let den = Rational.denominator e 
    if den = 1Q then None 
    else Some(Rational.numerator e, den)

let (|NegativeOne|NotNegativeOne|) = function
    | Number n when n = -1N -> NegativeOne
    | RealApproximation f when f = -1. -> NegativeOne
    | _ -> NotNegativeOne      

let (|Zero|NotZero|) = function
    | Number n when n = 0N -> Zero
    | RealApproximation f when f = 0. -> Zero
    | _ -> NotZero     

let (|One|NotOne|) = function
    | Number n when n = 1N -> One
    | RealApproximation f when f = 1. -> One
    | _ -> NotOne      
    
let (|Two|NotTwo|) = function
    | Number n when n = 2N -> Two
    | RealApproximation f when f = 2. -> Two
    | _ -> NotTwo 

let (|OneHalf|NotOneHalf|) = function
    | Number n when n = 1N/2N -> OneHalf
    | RealApproximation f when f = 0.5 -> OneHalf
    | _ -> NotOneHalf
            
let xIsMultipleOfy y x = x % y = 0

let inline rem n d =
    let rec loop n = if n >= d then loop (n-d) else n
    loop n   

let rec gcd c d = 
    match (abs c,abs d) with
    | (a, n) when n = 0N -> a
    | (a,b) -> gcd b (rem a b) 

let factorial (n : BigInteger) = List.fold (*) 1I [ 2I..n ] 

let rec factorialSymbolic (e : Expression) =
    match e with 
    | AsInteger m -> biginteger(factorial m)
    | _ -> failwith "Must be an integer"

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
    match Structure.productToIntConstantsAndVars x with
    | Some(ns, vs) -> Some(vs @ primefactors factorsExpr (abs ns), ns)
    | None -> None

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

let permutations n k = List.reduce (*) [ (n - k + 1I)..n ] 

let chooseN n k =   
    permutations n k / (factorial k)
    |> Expression.FromInteger

let expandChooseBinomial = function
    | Binomial(n,k) -> fac n /(fac k * fac(n - k))
    | x -> x

let sterlingsApproximation = function
    | Function(Fac, x) ->
        sqrt(2Q * Operators.pi * x) * (x/Constants.e)**x
    | x -> x

let approximateFactorial = function Function(Fac,x) -> (x/(Constants.e))**x | x -> x

let evalFactorial = function Function(Fac,x) -> factorialSymbolic x | x -> x

let evalBigIntLog = function
    | Function(Ln, AsInteger x) -> real (BigInteger.Log x)
    | x -> x
  
let tryNumber =
    function
    | Number n -> Some(float n)
    | IsRealNumber n -> Some(n.ToFloat().Value)
    | PositiveInfinity -> Some(Double.PositiveInfinity)
    | NegativeInfinity -> Some(Double.NegativeInfinity)
    | x -> Expression.toFloat x 
    | _ -> None

let xor a b = (a && not b) || (not a && b) 
   