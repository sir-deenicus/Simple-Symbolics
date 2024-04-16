module MathNet.Symbolics.NumberProperties

open Prelude.Math
open MathNet.Symbolics.Utils
open FSharp.Core.Operators
open Prelude.Common
open MathNet.Numerics
open MathNet
open System
open PeterO.Numbers
 
let pow10ToString = function 
    | x when x < 3 -> ""
    | 6 -> " million"
    | 9 -> " billion"
    | 12 -> " trillion"
    | 15 -> " quadrillion"
    | 18 -> " quintillion"
    | 21 -> " sextillion"
    | 24 -> " septillion"
    | 27 -> " octillion"
    | 30 -> " nonillion"
    | 33 -> " decillion"
    | 36 -> " undecillion"
    | 39 -> " duodecillion"
    | 42 -> " tredecillion"
    | 45 -> " quattuordecillion" 
    | x -> $"10^{x}" 

let pow10ToSIPrefix = function 
    | x when x < 3 -> ""
    | 6 -> " mega"
    | 9 -> " giga"
    | 12 -> " tera"
    | 15 -> " peta"
    | 18 -> " exa"
    | 21 -> " zetta"
    | 24 -> " yotta" 
    | x -> $"×10^{x} " 
     
let numberToEnglish n (x:float) =
    if x = 0. then "zero"
    elif x < 1_000_000. then 
        if n > 6 then string (log10bucket n x)
        else (log10bucket n x).ToString("N" + string n)
    else
        let p = floorf(log10f (absf x))
        let r = bucketRange 0 3. p
        sprintf "%g%s" (round n (x / 10. ** r)) (pow10ToString (int r))


type Numerics.BigInteger with
    static member FromString(str : string) =
        let nsign =
            if str.Length > 0 && str.[0] = '-' then -1I
            else 1I

        let charnums =
            let dl = Seq.toList str
            if nsign = -1I then dl.[1..]
            else dl

        let p = charnums.Length - 1

        let i, _ =
            charnums
            |> Seq.fold (fun (n, p) d ->
                n + bigint (int (string d)) * 10I ** p, p - 1) (0I, p)

        nsign * i

type ERational with
    static member FromBigRational(q:BigRational) =
        let n = EInteger.FromString(string q.Numerator)
        let d = EInteger.FromString (string q.Denominator)

        ERational.Create(n,d)

    static member ToBigRational(q:ERational) =
        let n = BigInteger.FromString(string q.Numerator)
        let d = BigInteger.FromString (string q.Denominator)
        BigRational.FromBigIntFraction(n,d)


module BigRational =
    let approximatelyInt x =
        if abs(floor x - x) < 0.000001 then true
        else
            let ratio = (floor x) / x
            ratio > 0.999999 && ratio < 1.000001

    ///limited by range of decimal (which is used as a less noisy alternative to floats)
    let fromRepeatingDecimal (df : Decimal) =
        let len = float ((string (df - floor df)).Length - 2)
        let pow10 = decimal (10. ** len)
        if abs df < 1M then
            BigRational.FromIntFraction
                (int (df * pow10), int (floor (pow10 - df)))
        else
            BigRational.FromIntFraction
                (int (df * pow10 - floor df), int (pow10 - 1M))

    let floor (q : BigRational) = q.Numerator / q.Denominator

    let ceil (q : BigRational) =
        if BigInteger.Remainder(q.Numerator, q.Denominator) <> 0I then
            floor q + 1I
        else floor q

    let log10 (q : BigRational) =
        BigInteger.Log10(q.Numerator) - BigInteger.Log10(q.Denominator)
        |> decimal |> BigRational.FromDecimal

    let log (q : BigRational) =
        BigInteger.Log(q.Numerator) - BigInteger.Log(q.Denominator)
        |> decimal |> BigRational.FromDecimal

    let fromFloat64 (f : float) =
        f |> ERational.FromDouble |> ERational.ToBigRational


    ///first index is sign of the number
    let decimalExpansion (q : BigRational) =
        let n, r, leadingZeros, numsign =
            let qnum, qden, nsign = BigInteger.Abs q.Numerator, BigInteger.Abs q.Denominator, q.Sign
            if qnum < qden && q <> 0N then
                let p10 =
                    ceilf (BigInteger.Log10(qden) - BigInteger.Log10(qnum))
                    |> int
                let num = qnum * 10I ** p10
                num / qden, BigInteger.Remainder(num, qden), p10, nsign
            else
                qnum / qden, BigInteger.Remainder(qnum, qden), 0, nsign

        let rec remloop p =
            seq {
                let d = p / q.Denominator
                let m = d * q.Denominator
                yield (int d)
                if p - m = 0I then ()
                else yield! (remloop ((p - m) * 10I))
            }

        seq {
            yield numsign
            yield! (List.replicate leadingZeros 0)
            yield (int n)
            yield! (remloop (r * 10I))
        }

    (*13/6 =
             2.1 (d)
       6 | 13
           12
            10 (input)
             6  (m)
             40  *)
    let decimalPart take (q:BigRational) =
        if q.Numerator < q.Denominator then
            //10 ** ceil (log10 q.Denominator)
            failwith "magnitude must be > 1"
        else
            let n = q.Numerator/ q.Denominator
            let r = BigInteger.Remainder(q.Numerator, q.Denominator)
            let rec remloop l steps p =
                if steps >= take then List.rev l, false
                else
                    let d = p / q.Denominator
                    let m = d * q.Denominator
                    if p-m = 0I then List.rev (d::l), true
                    else remloop (d::l) (steps + 1) ((p-m)*10I)
            n, remloop [] 0 (r*10I)


type Expression with
    member t.ToFormattedString() = expressionFormater t
    member t.ToFloat() = try Some (Evaluate.evaluate (Map.empty) t).RealValue with _ -> None
    member t.ToComplex() = (Evaluate.evaluate (Map.empty) t).ComplexValue
    member t.ToBigInt() =
        match t with
        | Number n -> Some (BigRational.floor n)
        | _ -> None 

    member t.ToInt() =
        match t with
        | Number n -> int n
        | _ -> failwith "not a number"

    member t.ToRational() =
        match t with
        | Number n -> Some n
        | _ -> None

let (|RealConstant|_|) =
    function
    | Constant Constant.I -> None
    | Constant c -> Some c
    | _ -> None

let (|RealApproximation|_|) =
    function
    | Approximation (Approximation.Real r) -> Some r
    | _ -> None
      
module Expression =
    open MathNet.Symbolics
    open System

    let fromDecimal f = BigRational.FromDecimal f |> Expression.FromRational
    let fromFloat64 f = BigRational.fromFloat64 f |> Expression.FromRational
    let fromDecimalRepeating n =
        BigRational.fromRepeatingDecimal n |> Expression.FromRational
    let toFloat (x : Expression) = x.ToFloat()
    let forceToFloat (x:Expression) = x.ToFloat() |> Option.get
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
        | Power(Approximation _, Approximation _)
        | Power(Constant _, Number _)
        | Power(Number _, Constant _)
        | Power(Constant _, Approximation _)
        | Power(Approximation _, Constant _)
        | Power(Constant _, Constant _)
        | Product [ Approximation _; Constant _ ]
        | Product [ Number _; Constant _ ]
        | Product [ Constant _; Constant _ ] ->
            true
        | _ -> false

    let isRealNumber =
        function
        | Number _ | RealConstant _ | RealApproximation _
        | Power(Number _, Number _)
        | Power(Number _, RealApproximation _)
        | Power(RealApproximation _, Number _)
        | Power(RealApproximation _, RealApproximation _)
        | Power(RealConstant _, Number _)
        | Power(Number _, RealConstant _)
        | Power(RealConstant _, RealConstant _)
        | Power(RealConstant _, RealApproximation _)
        | Power(RealApproximation _, RealConstant _)
        | Product [ RealApproximation _; Constant _ ]
        | Product [ Number _; RealConstant _ ]
        | Product [ Constant _; Constant _ ] ->
            true
        | _ -> false

    let isInteger =
        function
        | Number n when n.IsInteger -> true
        | _ -> false
 
    let isNegativeOrZeroNumber n =
        if isNumber n then
            n.ToFloat() |> Option.map (fun x -> x <= 0.)
        else None 

    let isNegativeNumber n =
        if isNumber n then
            n.ToFloat() |> Option.map (fun x -> x < 0.)
        else None

    let hasNegative = function
        | Product (Number n::_) -> Some(n < 0N)
        | x -> isNegativeNumber x

    let isPositiveNumber n =
        if isNumber n then
            match n.ToFloat() with
            | Some x -> Some(x >= 0.)
            | None -> None
        else None

    let rec isPositive = function
        | Function(Abs,_) -> Some true
        | Power(_,Number n) when (int n)%2 = 0 -> Some true
        | Sum l
        | Product l -> List.forall (fun x -> isPositive x = Some true) l |> Some
        | x -> isPositiveNumber x


module Approximation =
    let round n = function
        | Approximation(Real r) -> Approximation(Real (round n r))
        | IntervalF i ->
            let struct(l,r) = i.Pair
            IntervalF(IntSharp.Types.Interval.FromInfSup(round n l, round n r))
        | x -> x
        
    let toRational = function
        | Approximation (Approximation.Real r) -> Expression.FromRational (BigRational.fromFloat64 r)
        | x -> x
        
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

module Interval =
    let mapFloat f (i : IntSharp.Types.Interval) =
        let struct(l,r) = i.Pair
        IntSharp.Types.Interval.FromInfSup(f l, f r)

    let mapF f = function
        | IntervalF i -> 
            let i' = mapFloat f i
            if i'.Infimum = i'.Supremum then
                Expression.fromFloat64 i'.Infimum
            else IntervalF i'
        | x -> x

    let map f = function
        | Interval(l, r) -> Interval(f l, f r)
        | x -> x 
    
    let realLine = IntervalF IntSharp.Types.Interval.Entire

    let from a b = Interval(a,b)

    let upper = function
        | IntervalF i -> Expression.fromFloat64 i.Supremum
        | Interval(_,u) -> u
        | x -> x

    let lower = function
        | IntervalF i -> Expression.fromFloat64 i.Infimum
        | Interval(l,_) -> l
        | x -> x
    
///////////////////////////////////////////////
 

let (|NonIntegerRational|_|) = function
    | Number n when n.Denominator <> 1I -> Some((n.Numerator, n.Denominator))
    | _ -> None

let (|RationalLiteral|_|) r = function
    | Number n as q when n = BigRational.FromIntFraction r -> Some q
    | _ -> None

let (|IsRationalLiteral|_|) r = function
    | Number n when n = BigRational.FromIntFraction r -> Some()
    | _ -> None

let (|IntegerLiteral|_|) m = function
    | Number n as q when n.IsInteger && int n = m -> Some q
    | _ -> None

let (|BigIntegerEqualsRes|_|) m = function
    | Number n when n.IsInteger && int n = m -> Some (n.Numerator)
    | _ -> None

let (|IsIntegerLiteral|_|) m = function
    | Number n when n.IsInteger && int n = m -> Some()
    | _ -> None
      
let (|IsInteger|_|) = function
    | Number n as q when n.IsInteger -> Some q
    | _ -> None

let (|AsBigInteger|_|) = function
    | Number n when n.IsInteger -> Some n.Numerator
    | _ -> None

let (|IsNumber|_|) = function
      | e when Expression.isNumber e -> Some e
      | _ -> None

let (|IsRealNumber|_|) = function
      | e when Expression.isRealNumber e -> Some e
      | _ -> None

let (|AsFloatingPoint|_|) = function
    | IsRealNumber n -> n.ToFloat()
    | _ -> None

let (|SquareRoot|_|) = function
      | Power(e, n) when n = 1Q/2Q -> Some e
      | _ -> None

let (|IsNegativeNumber|_|) = function
      | e when Expression.isNegativeNumber e = Some true -> Some e
      | _ -> None


// match (a - b) with | Minus(a,b) -> Some(a,b) | _  -> None
// match (-a + b) with | Minus(a,b) -> Some(a,b) | _  -> None
// match (-4 + b) with | Minus(a,b) -> Some(a,b) | _  -> None
// match (b - 4) with | Minus(a,b) -> Some(a,b) | _  -> None
let (|Minus|_|) = function
      | Sum [Product [Number n; a]; b] when n = -1N -> Some (b,a)
      | Sum [a; Product [Number n; b]] when n = -1N -> Some (a,b)
      | Sum [Number n; a] when n < 0N -> Some(a, Number n)
      | _ -> None

let (|Divide|_|) e =
    let den = Rational.denominator e
    if den = 1Q then None
    else Some(Rational.numerator e, den)

let (|NegativeOne|_|) = function
    | Number n when n = -1N -> Some NegativeOne
    | RealApproximation f when f = -1. -> Some NegativeOne
    | _ -> None

let (|Zero|_|) = function
    | Number n when n = 0N -> Some Zero
    | _ -> None
 

let (|One|_|) = function
    | Number n when n = 1N -> Some One
    | RealApproximation f when f = 1. -> Some One
    | _ -> None

let (|Two|_|) = function
    | Number n when n = 2N -> Some Two
    | RealApproximation f when f = 2. -> Some Two
    | _ -> None

let (|OneHalf|_|) = function
    | Number n when n = 1N/2N -> Some OneHalf
    | RealApproximation f when f = 0.5 -> Some OneHalf
    | _ -> None

let xIsMultipleOfy y x = x % y = 0

let inline rem n d =
    let rec loop n = if n >= d then loop (n-d) else n
    loop n

let rec gcd c d =
    match (abs c,abs d) with
    | (a, n) when n = 0N -> a
    | (a,b) -> gcd b (rem a b)

let primeSeive n =
    let currentList = Hashset [2..n]

    let generateMarkeds p = [
        let mutable c = 2
        while c * p <= n do
            yield (c * p)
            c <- c + 1
    ]

    let rec gen p =
        let markeds = generateMarkeds p
        let clen = currentList.Count
        currentList.ExceptWith markeds
        if clen = currentList.Count then currentList
        else
            let prime = currentList |> Seq.find (fun i -> i > p)
            gen prime
    gen 2

let factorial (n : BigInteger) = List.fold (*) 1I [ 2I..n ]

let inline primefactors factor x =
    let rec loop x =
        match factor x with
        | Some [one] -> Some ([one])
        | Some [x; _] -> Some [x]
        | Some (_ :: (nextfactor :: _)) -> //first number is the largest, = input
            let r = x / nextfactor
            let f1, f2 = loop r, loop nextfactor 
            Option.map2 (@) f1 f2 
        | _ -> None 
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

let factorsExpr (e:Expression) =
    match e.ToBigInt() with 
    | None -> None 
    | Some n -> 
        if n > BigInteger(Int32.MaxValue) then None
        else e |> abs |> factors Expression.toInt Expression.FromInt32 |> Some

let internal groupPowers seal pl =
    List.groupBy id pl
    |> List.map (fun (x, l) ->
           if l.Length = 1 then seal x
           else Power(x, Expression.FromInt32(List.length l)))

let primefactorsPartial x =
    match Structure.productToIntConstantsAndVars x with
    | Some(ns, vs) -> 
        Option.map (fun factors -> vs @ factors, ns) (primefactors factorsExpr (abs ns))
    | None -> None

let primeFactorsExpr =
    abs
    >> primefactors factorsExpr
    >> Option.map (groupPowers hold >> Product)

let primeFactorsPartialExpr =
    primefactorsPartial
    >> Option.map (fst
                   >> groupPowers hold
                   >> Product)

let evalBigIntLog = function
    | Function(Ln, AsBigInteger x) -> ofFloat (BigInteger.Log x)
    | Function(Log, AsBigInteger x) -> ofFloat (BigInteger.Log10 x)
    | FunctionN(Log, [Number n; AsBigInteger x]) when n = 10N -> ofFloat (BigInteger.Log10 x)
    | x -> x 


let tryNumber =
    function
    | Number n -> Some(float n)
    | IsRealNumber n -> Some(n.ToFloat().Value)
    | PositiveInfinity -> Some(Double.PositiveInfinity)
    | NegativeInfinity -> Some(Double.NegativeInfinity)
    | x -> Expression.toFloat x

module Combinatorics =
    let permutations n k = List.fold (*) 1I [ (n - k + 1I)..n ]

    let chooseN n k =
        permutations n k / (factorial k)
        |> Expression.FromInteger

    let expandChooseBinomial = function
        | Binomial(n,k) -> fac n / (fac k * fac(n - k))
        | x -> x

    let factorialAsGamma = function 
        | Function(Fac, n) -> gamma(n + 1)
        | x -> x
        
    let stirlingsApproximation = function
        | Function(Fac, x) ->
            sqrt(2Q * Operators.pi * x) * (x/Constants.e)**x
        | x -> x

    let ramanujanFacApproximation = function
        | Function (Fac, x) -> 
            sqrt(Operators.pi) * (x/Constants.e)**x * (8 * x **3Q + 4 * x ** 2Q + x + 1/30Q) ** (1/6Q)
        | x -> x 

    ///approximate gamma function using Ramanujan's factorial approximation
    let gammaApproximationRamanujan = function
        | Function (Gamma, x) -> 
            ramanujanFacApproximation (fac (x - 1Q))
        | x -> x

    let gammaApproximationStirling = function
        | Function (Gamma, x) -> stirlingsApproximation (fac (x - 1Q)) 
        | x -> x

    let approximateFactorial = function Function(Fac,x) -> (x/(Constants.e))**x | x -> x

    let approximateGamma = function
        | Function (Gamma, x) -> approximateFactorial (fac (x - 1Q))
        | x -> x
        
    let evalFactorial = function Function(Fac,AsBigInteger m) -> ofBigInteger(factorial m) | x -> x
