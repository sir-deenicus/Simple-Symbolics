module MathNet.Symbolics.Core

open MathNet.Symbolics
open MathNet.Numerics
open System 
open MathNet.Symbolics.Utils
open Prelude.Common
 
//==========================================

let symbolString =
    function
    | Identifier(Symbol s) -> s
    | _ -> ""

let isSpecializedFunction = function
        | Probability
        | Gradient
        | Integral 
        | Expectation -> true
        | _ -> false

module List =
    let filterMap filter map xs =
        [ for x in xs do
              if filter x then yield map x ]

module BigRational =
    open Microsoft.FSharp.Core.Operators

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

    member t.Rational() =
        match t with
        | Number n -> n
        | _ -> failwith "not a number"

module Expression =
    let fromFloatDouble f =
        BigRational.fromFloatDouble f |> Expression.FromRational
    let fromFloat f = BigRational.fromFloat f |> Expression.FromRational
    let fromFloatRepeating f =
        BigRational.fromFloatRepeating f |> Expression.FromRational
    let toFloat (x : Expression) = x.ToFloat()
    let toInt (i : Expression) = i.ToInt()
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

    let evaluateFloat vars expr =
        let map =
            Seq.map (fun (x, y) -> symbolString x, FloatingPoint.Real y) vars
        let symbvals = System.Collections.Generic.Dictionary(dict map)
        try
            Some(let v = Evaluate.evaluate symbvals expr in v.RealValue)
        with _ -> None
        
    let rewriteAsOne x = Product [ x; x ** -1] 

    let groupSumsByDenominator = function
        | Sum l ->
            l |> List.groupBy Rational.denominator
              |> List.map (snd >> List.sum >> Rational.expand) 
              |> Sum
        | f -> f

    let toList =
        function
        | Sum l | Product l -> l
        | x -> [ x ]

    let isProduct =
        function
        | Product _ -> true
        | _ -> false

    let isSum =
        function
        | Sum _ -> true
        | _ -> false

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

    let isVariable =
        function
        | Identifier _ -> true
        | _ -> false 
    
    let isCompact =
        function
        | Identifier _ | Function _ | FunctionN(Probability, _) -> true
        | _ -> false    

    let isNegativePower =
        function
        | Power(_, Number n) -> n < 0N
        | _ -> false

    let isNegativeNumber =
        function
        | Approximation (Real r) -> r < 0. 
        | Number n -> n < 0N
        | _ -> false
    
    let cancelAbs =
        function
        | Function(Abs, x) -> x
        | x -> x 

    let containsLog =
        function
        | Function(Ln, _) -> true
        | _ -> false

    let containsTrig =
        function
        | Function(Cos, _) 
        | Function(Sin, _) 
        | Function(Acos, _) 
        | Function(Asin,_) 
        | Function(Atan,_) 
         | Function(Tan,_) ->
            true
        | _ -> false

    let toProductList = function
        | Product l -> l
        | f -> [f] 

    let consolidateNumerators = function
        | Sum l as f -> 
            let denominators = Hashset(List.map Rational.denominator l)
            if denominators.Count = 1 then 
               let d = Seq.head denominators
               let n = List.map Rational.numerator l |> Sum
               n / d 
            else f
        | f -> f

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
    | Number _ as n -> Some(n, [])
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

let rec simplifyRationals (roundto : int) =
    function
    | Number n as num ->
        let f = float n
        let pf = abs f
        if pf > 10000. || pf < 0.0001 then
            let p10 = floor (log10 pf)
            let x = Math.Round(f / 10. ** p10, roundto) |> Expression.fromFloat
            Product [ x
                      Power(10Q, p10 |> Expression.fromFloat) ]
        else num
    | Power(x, n) -> Power(simplifyRationals roundto x, n)
    | Sum l -> Sum(List.map (simplifyRationals roundto) l)
    | Product l -> Product(List.map (simplifyRationals roundto) l)
    | Function(f, x) -> Function(f, simplifyRationals roundto x)
    | x -> x

module Algebraic =
    let radicalRationalize x =
        let den = Rational.denominator x
        let num = Rational.numerator x
        num * den / (den * den)
    let simplifyNumericPower =
        function
        | Power(Number n, Number m) when m.IsInteger ->
            Expression.FromRational(n ** (int m))
        | f -> f

    let simplifySquareRoot (expr : Expression) =
        let sqRootGrouping =
            function
            | (Power(x, Number n)) when n > 1N ->
                if (int n % 2 = 0) then
                    x ** (Expression.FromRational(n / 2N)), 1Q
                elif n = 3N then x, x
                else x, simplifyNumericPower (Power(x, Number(n - 2N)))
            | x -> 1Q, x
        match expr with
        | Power(x, n) when n = 1Q / 2Q ->
            match primefactorsPartial x with
            | None -> None
            | Some(pfl, n) ->
                let n, (outr, inr) =
                    n,
                    pfl
                    |> groupPowers id
                    |> List.map sqRootGrouping
                    |> List.unzip

                let isneg = n.ToInt() < 0
                Some(List.fold (*) 1Q outr * sqrt (List.fold (*) (if isneg then
                                                                      -1Q
                                                                  else 1Q) inr))
        | _ -> None

    let collectNestedSumOrProduct test l =
        let innersums, rest = List.partition test l
        let ls = List.collect Expression.toList innersums
        ls @ rest

    let rec simplifyLite =
        function
        | Sum [ x ] | Product [ x ] -> simplifyLite x
        | Power(Number n, Number m) when m.IsInteger ->
            Expression.FromRational(n ** (int m))
        | Power(x, p) -> Power(simplifyLite x, simplifyLite p)        
        | Product (n::rest) when n = 1Q -> simplifyLite (Product rest)
        | Product l ->
            Product
                (List.map simplifyLite
                     (collectNestedSumOrProduct Expression.isProduct l))
        | Sum l ->
            Sum
                (List.map simplifyLite
                     (collectNestedSumOrProduct Expression.isSum l))
        | FunctionN(fn, l) -> FunctionN(fn, List.map simplifyLite l)
        | Function(fn, f) -> Function(fn, simplifyLite f) 
        | x -> x

    let simplify simplifysqrt fx =
        let rec simplifyLoop =
            function
            | Power(x, Number n) when n = 1N -> simplifyLoop x
            | Power(Number x, _) when x = 1N -> 1Q
            | Power(Product [ x ], n) | Power(Sum [ x ], n) ->
                simplifyLoop (Power(x, n))
            | Power(Number n, Number m) when m.IsInteger ->
                Expression.FromRational(n ** (int m))
            | Power(Power(x, a), b) -> simplifyLoop (Power(x, (a * b)))
            | Power(x, n) as expr when n = 1Q / 2Q && simplifysqrt ->
                match simplifySquareRoot expr with
                | Some x' -> x'
                | None -> Power(simplifyLoop x, n)
            | Power(x, n) -> Power(simplifyLoop x, simplifyLoop n)
            | Function(Atan, Number n) when n = 1N ->
                MathNet.Symbolics.Operators.pi / 4
            | Function(Atan, Number n) when n = 0N -> 0Q
            | Function(Cos, Product [ Number n; Constant Pi ]) when n = (1N / 2N) ->
                0Q
            | Function(Sin, Product [ Number n; Constant Pi ]) when n = (1N / 2N) ->
                1Q
            | Function(Cos, Product [ Number n; Constant Pi ]) when n = 1N / 4N ->
                1Q / sqrt (2Q)
            | Function(Sin, Product [ Number n; Constant Pi ]) when n = 1N / 4N ->
                1Q / sqrt (2Q)
            | Function(Ln, Function(Exp, x)) -> simplifyLoop x
            | Function(Exp, Function(Ln, x)) -> simplifyLoop x
            | Function(f, x) -> Function(f, (simplifyLoop x))
            | FunctionN(f, l) -> FunctionN(f, List.map simplifyLoop l)
            | Sum [ x ] | Product [ x ] -> simplifyLoop x
            | Product (n::rest) when n = 1Q -> simplifyLoop (Product rest)
            | Product l -> List.map simplifyLoop l |> List.fold (*) 1Q
            | Sum l -> List.map simplifyLoop l |> List.sum
            | x -> x
        simplifyLoop fx |> Rational.reduce

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

let rec factorial (n : BigRational) =
    if n = 1N then 1N
    else n * factorial (n - 1N)

let rec factorialSymb (e : Expression) =
    match e with 
    | Number m when m < 15N -> Number(factorial m)
    | _ -> failwith "Must be a number < 15"

let choose n k = 
    let bn, bk = BigRational.FromInt n, BigRational.FromInt k
    if k = 0 || n = k then 1Q 
    else
        factorial bn / (factorial bk * (factorial (bn - bk))) 
        |> Expression.FromRational
    
open Operators
open System.Collections.Generic

let ln = Operators.ln
let arctan = Operators.arctan
let sec = Operators.sec

let symbol = symbol
let V = symbol
let sy = symbol
let mkSymbolMap l = l |> List.map (fun s -> s, symbol s) |> Map
 
type Units(q : Expression, u : Expression, ?altUnit) =
    let mutable altunit = defaultArg altUnit ("")

    static member numstr =
        function
        | Number(x) when x = 1000N -> "kilo"
        | Number(x) when x = 1000_000N -> "mega"
        | Number(x) when x = 1_000_000_000N -> "giga"
        | Number(x) when x = 1_000_000_000_000N -> "tera"
        | Number x when x = 1N -> ""
        | x -> x.ToFormattedString()

    member __.Quantity = q
    member __.Unit = u

    member __.AltUnit
        with get () = altunit
        and set u = altunit <- u 
    
    member t.EvaluateQuantity(m) =
        Expression.evaluateFloat m q

    member t.EvaluateQuantity () = q.ToFloat()
    member __.ToAltString() = sprintf "%s %s" (u.ToFormattedString()) altunit
    static member Zero = Units(0Q, 0Q)

    static member (+) (a : Units, b : Units) =
        if a.Unit = b.Unit then
            Units(a.Quantity + b.Quantity, a.Unit, a.AltUnit)
        elif b.Unit = 0Q then Units(a.Quantity, a.Unit, a.AltUnit)
        elif a.Unit = 0Q then Units(b.Quantity, b.Unit, b.AltUnit)
        else failwith "Units don't match"

    static member (~-) (a : Units) = (-a.Quantity, a.Unit, a.AltUnit)
    static member (-) (a : Units, b : Units) = a + -1 * b
    static member (*) (a : Units, b : Units) =
        Units
            (a.Quantity * b.Quantity, a.Unit * b.Unit,
             a.AltUnit + " " + b.AltUnit)
    static member (*) (a : Units, b : Expression) =
        Units(a.Quantity * b, a.Unit, a.AltUnit)
    static member (*) (a : Units, b : int) =
        Units(a.Quantity * b, a.Unit, a.AltUnit)
    static member (*) (a : int, b : Units) = Expression.FromInt32 a * b

    static member (*) (a : Units, b : float) =
        Units(a.Quantity * real b, a.Unit, a.AltUnit)
    static member (*) (a : float, b : Units) = real a * b

    static member (*) (a : Expression, b : Units) =
        Units(a * b.Quantity, b.Unit,
              Units.numstr a + (if b.AltUnit = "" then
                                    b.Unit.ToFormattedString()
                                else b.AltUnit))

    static member Abs(a : Units) = Units(abs a.Quantity, a.Unit, a.AltUnit)
    static member Pow(a : Units, b : int) =
        Units(a.Quantity ** b, a.Unit ** b, a.AltUnit + "^" + string b)
    static member Pow(a : Units, b : Expression) =
        Units
            (Algebraic.simplify true (a.Quantity ** b),
             Algebraic.simplify true (a.Unit ** b))
    static member (/) (a : Units, b : Expression) =
        Units(a.Quantity / b, a.Unit, a.AltUnit)
    static member (/) (a : Units, b : Units) =
        Units
            (a.Quantity / b.Quantity, a.Unit / b.Unit,
             a.AltUnit + "/" + b.AltUnit)
    static member (/) (a : Expression, b : Units) =
        Units(a / b.Quantity, 1 / b.Unit, b.AltUnit + "^-1")

    static member To(a : Units, b : Units) =
        if a.Unit = b.Unit then
            let altunit =
                if b.AltUnit = "" then
                    Units.numstr b.Quantity + " " + b.Unit.ToFormattedString()
                else b.AltUnit

            let qstr =
                if Expression.isNumber (a / b).Quantity then
                    let q, r = ((a / b).Quantity.ToFloat() |> smartroundEx 1)
                    Expression.toSciNumString r q
                else (a / b).Quantity.ToFormattedString()
            let space = if expressionFormat = "Infix" then " " else "\\;"    
            Some(sprintf "%s%s%s" qstr space altunit, qstr.Length)
        else None

    static member ToUnitQuantity(a : Units, b : Units) =
        if a.Unit = b.Unit then   
            Some((a / b).Quantity)
        else None

    override t.ToString() =
        let space = if expressionFormat = "Infix" then " " else "\\;"
        if Expression.isNumber t.Quantity then
            let q, r = t.Quantity.ToFloat() |> smartroundEx 1
            let qstr = Expression.toSciNumString r q
            if t.Unit = 1Q then qstr
            else sprintf "%s%s%s" qstr space (t.Unit.ToFormattedString())
        else
            sprintf "%s%s%s" (t.Quantity.ToFormattedString()) space
                (t.Unit.ToFormattedString())

module UnitsDesc =
    let power = symbol "power"
    let energy = symbol "energy"
    let force = symbol "force"
    let energyflux = symbol "energyflux"
    let volume = symbol "volume"
    let velocity = symbol "velocity"
    let accel = symbol "accel"
    let time = symbol "time"
    let mass = symbol "mass"
    let length = symbol "length"
    let temperature = symbol "temperature"
    let current = symbol "current"
    let currency = V"currency" 

    let Names =
         set
          [ "power"
            "energy"
            "force"
            "energyflux"
            "volume"
            "velocity"
            "accel"
            "time"
            "mass"
            "length"
            "temperature"
            "current" ]

module Units = 

    let setAlt alt (u : Units) =
        u.AltUnit <- alt
        u

    let unitless = Units(1Q, 1Q, "")
    let micro = Expression.fromFloat 1e-6
    let milli = Expression.fromFloat (0.001)
    let centi = Expression.FromRational(1N / 100N)
    let kilo = 1000Q
    let mega = 1_000_000Q
    let million = mega
    let giga = 1_000_000_000Q
    let billion = giga
    let tera = 1_000_000_000_000Q
    let peta = 10Q ** 15
    let exa = 10Q ** 18
    //----------Temperature
    let K = Units(1Q, symbol "K", "K")
    let celsius = Units(real -273.15, symbol "K", "°C") 
    //----------
    let gram = Units(1Q, Operators.symbol "g", "g")
    let kg = kilo * gram |> setAlt "kg"

    let meter = Units(1Q, Operators.symbol "meters", "meter")
    let km = 1000Q * meter |> setAlt "km"
    let cm = centi * meter |> setAlt "cm"
    let ft = Expression.FromRational(BigRational.fromFloat 0.3048) * meter
    let yard = 3 * ft
    let inches = 12 * ft
    let au =  150Q * mega * km |> setAlt "AU" 
    //----------
    let sec = Units(1Q, Operators.symbol "sec", "sec")
    let minute = 60Q * sec |> setAlt "minute"
    let minutes = minute |> setAlt "minutes"
    let hr = 60Q * minute |> setAlt "hr"
    let hrs = hr |> setAlt "hrs"
    let days = 24Q * hr |> setAlt "days"
    let day = days |> setAlt "day"
    let month = 30.4167 * day |> setAlt "month"
    let months = month
    let weeks = 7Q * days |> setAlt "weeks"
    let years = 52Q * weeks |> setAlt "years"
    let year = years |> setAlt "year"
    //----------
    let N = kg * meter / sec ** 2 |> setAlt "N"

    let J = kg * meter ** 2 * sec ** -2 |> setAlt "J"
    let kJ = (J * 1000Q) |> setAlt "kJ"
    let calorie = Expression.fromFloat 4.184 * J |> setAlt "calorie"
    let btu = Expression.FromRational(BigRational.fromFloat 1055.06) * J

    let W = (J / sec) |> setAlt "W"
    let watts = W |> setAlt "W"
    let kW = (W * 1000Q) |> setAlt "kW"

    let kWh = (kW * hr) |> setAlt "kWh"

    let amps = Units(1Q, Operators.symbol "Amps", "Amps")
    let amp = amps |> setAlt "amp"
    let C = amps * sec |> setAlt "coulombs"
    let volt = J / C |> setAlt "volt"
    let volts = volt |> setAlt "volts"
    //----------
    let bits = Units(1Q, Operators.symbol "bits")
    let bytes = 8Q * bits |> setAlt "bytes"
    let gigabytes = giga * bytes |> setAlt "gigabytes"

    let flop = Units(1Q, Operators.symbol "flop")
    let exafloatops = exa * flop |> setAlt "exafloatops"
    let terafloatops = tera * flop |> setAlt "terafloatops"
    
    let flops = flop / sec |> setAlt "flop/s"
    let gigaflops = giga * flops |> setAlt "gigaflop/s"
    let teraflops = tera * flops |> setAlt "teraflop/s"

    let usd = Units(1Q, symbol "USD", "USD")

    let planck = Expression.fromFloatDouble 6.62607004e-34 * J * sec
    let G = Expression.fromFloat 6.674e-11 * meter ** 3 * kg ** -1 * sec ** -2
    let hbar = planck / (2 * pi)
    let speed_of_light = 299_792_458 * meter / sec
    let stefan_boltzman =
        Expression.fromFloat 5.670367e-8 * W * meter ** -2 * K ** -4
    let boltzman_constant = Expression.fromFloat 1.38064852e-23 * J / K
    //==============
    let integrateWith (integral:Expression->Expression) (dx:Units) (fx : Units) = 
        Units(integral fx.Quantity, fx.Unit, fx.AltUnit + " " + dx.AltUnit) * dx 

    let differentiate (dy : Units) (dx : Units) =
        Units
            (Calculus.differentiate dy.Quantity dx.Quantity, dx.Unit / dy.Unit,
             dx.AltUnit + "/" + dy.AltUnit)

    let units =
        [ W, "Power"
          kW, "Power"
          mega * W |> setAlt "megawatts", "Power"
          giga * W |> setAlt "gigawatts", "Power"
          tera * W |> setAlt "terawatts", "Power"
          J, "Energy"
          kJ, "Energy"
          mega * J |> setAlt "megajoules", "Energy"
          kWh, "Energy"
          amps * hr |> setAlt "amp hours", "Charge"
          terafloatops, "computation"
          exafloatops, "computation"
          flop, "computation"
          N, "Force"
          K, "Temperature"
          W / meter ** 2, "Energy flux"
          W / cm ** 2, "Energy flux"
          bytes, "information"
          gigabytes, "information"
          tera * bytes, "information"
          flops, "flop/s"
          gigaflops, "flop/s"
          teraflops, "flop/s"
          meter ** 3, "volume"
          meter / sec, "velocity"
          meter / sec ** 2, "Acceleration"
          minute, "Time"
          hr, "Time"
          years, "Time"
          weeks, "Time"
          days, "Time"
          sec, "Time"
          gram, "mass"
          kg, "mass"
          meter, "length"
          km, "length" ]

    let simplifyUnits (u : Units) =
        let matched =
            List.filter (fun (um : Units, _) -> u.Unit = um.Unit) units
            |> List.map (fun (u', t) ->
                   let s, len = Units.To(u, u') |> Option.get
                   len, s + space() + "(" + t + ")")
        match matched with
        | [] -> u.ToString()
        | l ->
            l
            |> List.minBy fst
            |> snd

    let rec replaceUnitPlaceHolders (defs : seq<Expression * Units>) e =
        let map = dict defs
        let unitstest l =
            let hs = Hashset(l |> List.map (fun (u:Units) -> u.Unit))
            hs.Count = 1 || (hs.Count = 2 && hs.Contains 1Q)
        let rec replace = function
            | Identifier _ as v when map.ContainsKey v -> map.[v]
            | Power(x, p) -> (replace x) ** p
            | Sum l -> List.sumBy replace l
            | Product l ->
                l
                |> List.fold (fun p x -> p * (replace x))
                       (Units(1Q, 1Q))
            | FunctionN(Max, l) as f ->
                match List.map replace l with
                | l' when (l'
                           |> List.forall
                                  (fun u -> Expression.isNumber u.Quantity)
                           && unitstest l') ->
                    let largest = l' |> List.maxBy (fun u -> u.Quantity.ToFloat())
                    let units = l' |> List.find (fun u -> u.Unit <> 1Q)
                    Units(largest.Quantity, units.Unit)
                | _ -> Units(f, 1Q)
            | f -> Units(f, 1Q)
        replace e

    let tryreplaceUnitPlaceHolders vars e =
        try
            let u = replaceUnitPlaceHolders vars e
            u.EvaluateQuantity() |> ignore
            Some u
        with _ -> None

    let map f (q:Units) =
        Units(f q.Quantity, q.Unit )
         
    let toUnitQuantity (b : Units) (a : Units) =
        if a.Unit = b.Unit then   
            Some((a / b).Quantity)
        else None

    let toUnitOption (a : Units) (b : Units) = 
        if a.Unit = b.Unit then   
            Some((a / b).Quantity)
        else None

    let toUnitOptionValue (a : Units) (b : Units) = 
        toUnitOption a b |> Option.get 

    let toUnitQuantityValue (a : Units) (b : Units) = 
        toUnitQuantity a b |> Option.get 

    let toCelsius (u:Units) = 
        if u.Unit = V"K" then
            Some(u.Quantity - 273.15)
        else None
    let inline celsiusToFahrenheit c =
        Expression.toFloat(c * 9Q/5Q + 32Q)
    let fahrenheitToCelsius f =
        5Q/9Q * (f - 32Q) |> Expression.toFloat
    let fromCelsius (x:float) =
        (x + 273.15) * K

let rec replaceWithIntervals (defs : seq<Expression * IntSharp.Types.Interval>) e =
    let map = dict defs 
    let rec replace = function
        | Identifier _ as v when map.ContainsKey v -> Some map.[v]
        | Sum l -> 
            List.map replace l 
            |> List.filterMap Option.isSome Option.get 
            |> List.sum 
            |> Some
        | Product l ->
            List.map replace l 
            |> List.filterMap Option.isSome Option.get 
            |> List.fold (*)
                    (IntSharp.Types.Interval.FromDoublePrecise 1.)
            |> Some
        | FunctionN(Max, l) ->
            match l with
            | l' when (l' |> List.forall Expression.isNumber) ->
                let largest = l' |> List.map (fun x -> x.ToFloat()) |> List.max
                IntSharp.Types.Interval.FromDoubleWithEpsilonInflation largest
                |> Some
            | _ -> None
        | _ -> None
    replace e 

let rec containsVar x =
    function
    | Identifier _ as sy when sy = x -> true
    | Power(p, n) -> containsVar x n || containsVar x p
    | Function(_, fx) -> containsVar x fx
    | Product l | Sum l | FunctionN(_, l) -> List.exists (containsVar x) l
    | _ -> false

let rec containsAnyVar =
    function
    | Identifier _ -> true
    | Power(p, n) -> containsAnyVar n || containsAnyVar p
    | Function(_, fx) -> containsAnyVar fx
    | Product l | Sum l | FunctionN(_, l) -> List.exists containsAnyVar l
    | _ -> false

let rec replaceSymbol r x =
    function
    | Identifier _ as var when var = x -> r
    | Power(f, n) -> Power(replaceSymbol r x f, replaceSymbol r x n)
    | Function(fn, f) -> Function(fn, replaceSymbol r x f)
    | Product l -> Product(List.map (replaceSymbol r x) l)
    | Sum l -> Sum(List.map (replaceSymbol r x) l)
    | FunctionN(fn, l) -> FunctionN(fn, List.map (replaceSymbol r x) l)
    | x -> x

let replaceSymbols (vars : seq<_>) e =
    let map = dict vars
    let rec loop = function
        | Identifier _ as var when map.ContainsKey var -> map.[var]
        | Power(f, n) -> Power(loop f, loop n)
        | Function(fn, f) -> Function(fn, loop f)
        | Product l -> Product(List.map loop l)
        | Sum l -> Sum(List.map loop l)
        | FunctionN(fn, l) -> FunctionN(fn, List.map loop l)
        | x -> x
    loop e

let rec replaceVariableSymbol replacer =
    function
    | Identifier(Symbol s) -> Identifier(Symbol(replacer s))
    | Power(f, n) ->
        Power
            (replaceVariableSymbol replacer f,
             replaceVariableSymbol replacer n)
    | Function(fn, f) ->
        Function(fn, replaceVariableSymbol replacer f)
    | Product l ->
        Product(List.map (replaceVariableSymbol replacer) l)
    | Sum l -> Sum(List.map (replaceVariableSymbol replacer) l)
    | FunctionN(fn, l) ->
        FunctionN(fn, List.map (replaceVariableSymbol replacer) l)
    | x -> x

let rec findVariablesOfExpression =
    function
    | Identifier _ as var -> [ var ]
    | Power(x, n) -> findVariablesOfExpression x @ findVariablesOfExpression n
    | Product l | Sum l | FunctionN(_, l) ->
        List.collect findVariablesOfExpression l
    | Function(_, x) -> findVariablesOfExpression x
    | _ -> []

let replaceExpression replacement expressionToFind formula =
    let tryReplaceCompoundExpression replacement
        (expressionToFindContentSet : Hashset<_>) (expressionList : _ list) =
        let expressionListSet = Hashset expressionList
        if expressionToFindContentSet.IsSubsetOf expressionListSet then
            expressionListSet.SymmetricExceptWith expressionToFindContentSet
            replacement :: List.ofSeq expressionListSet
        else expressionList

    let expressionToFindContentSet = Hashset(Expression.toList expressionToFind)

    let rec iterReplaceIn =
        function
        | Identifier _ as var when var = expressionToFind -> replacement
        | FunctionN _ | Power _ | Function _ | Number _ | Constant _ as expr 
            when expr = expressionToFind ->
                replacement
        | Power(p, n) -> Power(iterReplaceIn p, iterReplaceIn n)
        | Function(f, fx) -> Function(f, iterReplaceIn fx)
        | Product l ->
            Product
                (l |> List.map iterReplaceIn
                   |> (tryReplaceCompoundExpression replacement
                          expressionToFindContentSet))
        | Sum l ->
            Sum
                (l |> List.map iterReplaceIn
                   |> (tryReplaceCompoundExpression replacement
                          expressionToFindContentSet))
        | FunctionN(Probability, s::x::rest) -> FunctionN(Probability, s::iterReplaceIn x::rest) 
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn -> FunctionN(fn, [iterReplaceIn x; param])
        | FunctionN(fn, l) ->
            FunctionN (fn, List.map iterReplaceIn l)
        | x -> x
    iterReplaceIn (Algebraic.simplifyLite formula) |> Algebraic.simplify true

let containsExpression expressionToFind formula =
    let tryFindCompoundExpression (expressionToFindContentSet : Hashset<_>)
        (expressionList : _ list) =
        let expressionListSet = Hashset expressionList
        expressionToFindContentSet.IsSubsetOf expressionListSet

    let expressionToFindContentSet = Hashset(Expression.toList expressionToFind)

    let rec iterFindIn =
        function
        | Identifier _ as var when var = expressionToFind -> true
        | Power(p, n) as powr ->
            powr = expressionToFind || iterFindIn p || iterFindIn n
        | Function(_, fx) as fn -> fn = expressionToFind || iterFindIn fx
        | Product l as prod ->
            prod = expressionToFind
            || tryFindCompoundExpression expressionToFindContentSet l
            || (List.exists iterFindIn l)
        | Sum l as sum ->
            sum = expressionToFind
            || tryFindCompoundExpression expressionToFindContentSet l
            || (List.exists iterFindIn l)
        | FunctionN(_, l) as func ->
            func = expressionToFind
            || (List.exists iterFindIn l)
        | _ -> false
    iterFindIn (Algebraic.simplifyLite formula)

let rec width =
    function
    | Undefined
    | Constant _
    | Identifier _ -> 1
    | Power(x, n) -> width x + 1 + width n
    | FunctionN(fn, x::_) when isSpecializedFunction fn -> width x + 1
    | Product l | Sum l | FunctionN(_, l) -> List.sumBy width l
    | Function(_, x) -> width x + 1
    | Approximation _ | Number _ -> 1
    | f -> failwith (sprintf "unimplemented compute size %A" (  f))

let rec depth =
    function
    | Undefined 
    | Constant _
    | Identifier _ -> 1
    | Power(x, n) -> (max (depth x) (depth n)) + 1
    | FunctionN(fn, x::_) when isSpecializedFunction fn -> depth x + 1
    | Product l | Sum l | FunctionN(_, l) -> 1 + (List.map depth l |> List.max)
    | Function(_, x) -> depth x + 1
    | Approximation _ | Number _ -> 1
    | f -> failwith ("unimplemented compute depth for " + (f.ToFormattedString()))

let averageDepth =
    function
    | Sum l | Product l | FunctionN(_, l) -> List.averageBy (depth >> float) l
    | e -> float (depth e)

let averageWidth =
    function
    | Sum l | Product l | FunctionN(_, l) -> List.averageBy (width >> float) l
    | e -> float (depth e)

module Structure =
    let rootWidth =
        function
        | Sum l | Product l -> List.length l
        | _ -> -1
    let partition func =
        function
        | Sum l -> 
            let a,b = List.partition func l   
            List.sum a, List.sum b
        | Product l -> 
            let a,b = List.partition func l  
            List.fold (*) 1Q a, List.fold (*) 1Q b 
        | f -> if func f then f, undefined else undefined, f

    let filter func =
        function
        | Sum l -> 
            List.filter func l 
            |> List.sum
        | Product l -> 
            List.filter func l   
            |> List.fold (*) 1Q  
        | f -> if func f then f else undefined

    let exists func =
        function
        | Sum l | Product l | FunctionN(_, l) -> List.exists func l
        | f -> func f

    let rec existsRecursive func =
        function
        | Undefined as un -> func un
        | Identifier _ as i -> func i
        | Power(p, n) as pow ->
            func pow || existsRecursive func n || existsRecursive func p
        | Function(_, fx) as f -> func f || existsRecursive func fx
        | (Product l | Sum l | FunctionN(_, l)) as prod ->
            func prod || List.exists (existsRecursive func) l
        | _ -> false
  
    let rec first func =
        function
        | Identifier _ as i ->
            if func i then Some i
            else None
        | Power(p, n) as pow ->
            if func pow then Some pow
            else List.tryPick (first func) [ p; n ]
        | Function(_, fx) as f ->
            if func f then Some f
            else first func fx 
        | FunctionN(fn, x::param::_ ) as f when isSpecializedFunction fn -> 
            if func f then Some f
            else first func x 
        | (Product l | Sum l | FunctionN(_, l)) as prod ->
            if func prod then Some prod
            else List.tryPick (first func) l
        | _ -> None

    let collectDistinctWith f expr =
        Structure.collectAllDistinct (fun x ->
            if f x then Some x
            else None) expr

    let rec removeSymbol x =
        function
        | Identifier _ as var when var = x -> None
        | Power(f, n) ->
            maybe {
                    let! g = removeSymbol x f  
                    let! m = removeSymbol x n  
                    return Power(g, m)} 
        | Function(fn, f) ->
            removeSymbol x f |> Option.map (fun g -> Function(fn, g))
        | Product l ->
            Product
                (List.map (removeSymbol x) l
                 |> List.filterMap Option.isSome Option.get) |> Some
        | Sum l ->
            Sum
                (List.map (removeSymbol x) l
                 |> List.filterMap Option.isSome Option.get) |> Some
        | FunctionN(fn, l) ->
            match List.map (removeSymbol x) l
                 |> List.filterMap Option.isSome Option.get with
            | [] -> None
            | nl -> FunctionN (fn, nl) |> Some
        | x -> Some x

    let rec recursiveFilter filter =
        function
        | Number _ as n when not (filter n) -> None
        | Number _ as n -> Some n
        | Identifier _ as var when not (filter var) -> None
        | Identifier _ as var -> Some var
        | Power(f, n) as p ->
            match 
                (maybe {
                    let! g = recursiveFilter filter f  
                    let! m = recursiveFilter filter n  
                    return Power(g, m)}) with
            | None -> if filter p then Some p else None
            | f -> f
        | Product l as prod ->
            let pr = List.map (recursiveFilter filter) l
                     |> List.filterMap Option.isSome Option.get
            match pr with 
            | [] -> if filter prod then Some prod else None
            | l -> Some (List.fold (*) 1Q l)
        | Sum l as sum ->
            let suml = List.map (recursiveFilter filter) l
                     |> List.filterMap Option.isSome Option.get
            match suml with 
            | [] -> if filter sum then Some sum else None
            | l -> Some (List.sum l) 
        | Function _ 
        | FunctionN _ as fn -> 
            if filter fn then Some fn else None   
        | _ -> None

    let rec applyInFunctionsRec fx =
        function  
        | Function(fn, f) -> Function(fn, applyInFunctionsRec fx f)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability,
                        s::applyInFunctionsRec fx x::rest)
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn ->
            FunctionN(fn, [ applyInFunctionsRec fx x;param ]) 
        | x -> fx x
    let applyInFunctions fx =
        function  
        | Function(fn, f) -> Function(fn,fx f)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability,
                            s::fx x::rest)
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn ->
            FunctionN(fn, [fx x;param ]) 
        | x -> x
    let rec recursiveMap fx =
        function
        | Identifier _ as var -> fx var
        | Power(f, n) -> fx (Power(recursiveMap fx f, recursiveMap fx n))
        | Function(fn, f) -> fx (Function(fn, recursiveMap fx f))
        | Product l -> fx (Product(List.map (recursiveMap fx) l))
        | Sum l -> fx (Sum(List.map (recursiveMap fx) l))
        | FunctionN(Probability, s::x::rest) ->
            fx (FunctionN(Probability,
                            s::recursiveMap fx x::rest))
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn ->
            fx (FunctionN(fn,
                          [ recursiveMap fx x
                            param ]))
        | FunctionN(fn, l) -> fx (FunctionN(fn, List.map (recursiveMap fx) l))
        | x -> fx x 

    let mapfirst func expr =
        let mutable isdone = false
        recursiveMap (function
            | f when not isdone ->
                let f' = func f
                isdone <- f' <> f
                f'
            | f -> f) expr 

    let removeExpression x f =
        let placeholder = symbol "__PLACE_HOLDER__"
        let replaced = replaceExpression placeholder x f
        removeSymbol placeholder replaced

type Expression with
    static member groupInSumWith var = function
        | Sum l -> 
            let haves, nots = List.partition (containsExpression var) l
            Product[var; haves |> List.sumBy (fun x -> x/var)] + Sum nots
        | f -> f 

    static member toRational e =
        let e' = Trigonometric.simplify e |> Algebraic.simplify true
        match e' with
        | Number(n) -> n
        | _ ->
            failwith
                (sprintf "not a number : %s => %s | %A" (e.ToFormattedString())
                     (e'.ToFormattedString()) e')

    static member FullSimplify e =
        e
        |> Algebraic.simplify true
        |> Algebraic.simplify true
        |> Rational.rationalize
        |> Algebraic.expand

    static member FullerSimplify e =
        Trigonometric.simplify e
        |> Algebraic.simplify true
        |> Algebraic.simplify true
        |> Rational.rationalize
        |> Algebraic.expand

    static member isNumericOrVariable anyVar =
        let keep s =
            anyVar || Strings.strcontains "Var" s
            || UnitsDesc.Names.Contains s
        function 
        | Identifier(Symbol s) when keep s -> true
        | IsNumber _ -> true 
        | Function (_, IsNumber _) -> true 
        | FunctionN(Max, [a;b]) ->
            match(a,b) with
            | Identifier(Symbol s), Identifier(Symbol s2) 
                when keep s && keep s2 -> true
            | Identifier(Symbol s), IsNumber _   
            | IsNumber _ , Identifier(Symbol s) 
                when keep s -> true
            | Product l, IsNumber _
            | Sum l, IsNumber _  
            | Product l, IsNumber _
            | IsNumber _ , Sum l
            | IsNumber _, Product l 
                when List.filter Expression.isVariable l 
                    |> List.forall (symbolString >> keep) -> true 
            | Identifier(Symbol s), Sum l
            | Identifier(Symbol s), Product l
            | Sum l, Identifier(Symbol s)
            | Product l, Identifier(Symbol s) 
                when keep s && 
                    List.filter Expression.isVariable l 
                    |> List.forall (symbolString >> keep) -> true 
            | IsNumber _ , IsNumber _ -> true
            | _ -> false
        | FunctionN(_, l) -> not (List.exists (Expression.isNumber >> not) l)
        | _ -> false


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
    override __.ToString() =
        leq.ToFormattedString() + " = " + req.ToFormattedString()

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
            | Leq -> match expressionFormat with InfixFormat -> " ≤ " | _ -> " \\leq "
            | Geq -> match expressionFormat with InfixFormat -> " ≥ " | _ -> " \\geq "
    let flipComparer = function
    | Lesser -> Greater
    | Greater -> Lesser
    | Leq -> Geq    
    | Geq -> Leq

type InEquality(comparer:InEquality.Comparer, leq : Expression, req : Expression) =
    member __.Definition = leq, req
    member __.Left = leq
    member __.Right = req
    member __.InEqualities =
        [ leq, req
          req, leq ] 
    override __.ToString() =
        leq.ToFormattedString() + string comparer + req.ToFormattedString()

type InEqualityU(comparer:InEquality.Comparer, leq : Units, req : Units) =
    member __.Definition = leq, req
    member __.Left = leq
    member __.Right = req
    member __.Comparer = comparer

    member __.InEqualities =
        [ leq, req
          req, leq ]
    override __.ToString() =
        (Units.simplifyUnits leq) + string comparer + (Units.simplifyUnits req)
    member __.ToStringAs(u:Units) =
        let ul, _ = Units.To(leq, u).Value
        let rl, _ = Units.To(req, u).Value
        ul + string comparer + rl   
    member __.Flip() =
        InEqualityU(InEquality.flipComparer comparer, req, leq)
    member __.FlipSign() =
        InEqualityU(InEquality.flipComparer comparer, leq, req)
    member i.ApplyToRight f = InEqualityU(i.Comparer, i.Left, f i.Right)
    member i.ApplyToLeft f = InEqualityU(i.Comparer, f i.Left, i.Right)
    member i.Apply f = InEqualityU(i.Comparer, f i.Left, f i.Right)
    static member (+) (eq : InEqualityU, expr : Units) =
        InEqualityU(eq.Comparer, eq.Left + expr, eq.Right + expr)
    static member (+) (eq : InEqualityU, expr : Expression) =
        eq + (expr * Units.unitless)
    static member (-) (eq : InEqualityU, expr : Units) =
        InEqualityU(eq.Comparer, eq.Left - expr, eq.Right - expr)
    static member (/) (eq : InEqualityU, expr : Expression) =
        eq / (expr * Units.unitless)
    static member (/) (eq : InEqualityU, expr : Units) =
        let c = if Expression.isNegativeNumber expr.Quantity then 
                    InEquality.flipComparer eq.Comparer
                else eq.Comparer
        InEqualityU(c, eq.Left / expr, eq.Right / expr)

type InEqualityU with
    static member applyToRight f (i:InEqualityU) =
        InEqualityU(i.Comparer, i.Left, f i.Right)
    static member applyToLeft f (i:InEqualityU) =
        i.ApplyToLeft f
    static member apply f (i:InEqualityU) = i.Apply f 

let lequ (a:Units) (b:Units) = InEqualityU(InEquality.Comparer.Leq,a,b)
let gequ (a:Units) (b:Units) = InEqualityU(InEquality.Comparer.Geq,a,b)
let ltu (a:Units) (b:Units)  = InEqualityU(InEquality.Comparer.Lesser,a,b)
let gtu (a:Units) (b:Units)  = InEqualityU(InEquality.Comparer.Greater,a,b)        
let leq a b = InEquality(InEquality.Comparer.Leq,a,b)
let geq a b = InEquality(InEquality.Comparer.Geq,a,b)
let lt a b = InEquality(InEquality.Comparer.Lesser,a,b)
let gt a b = InEquality(InEquality.Comparer.Greater,a,b)

module Equation =
    let swap (eq:Equation) = Equation(swap eq.Definition) 
    let right (eq:Equation) = eq.Right
    let left (eq:Equation) = eq.Left

let (<=>) a b = Equation(a, b)

let equals a b = Equation(a, b)

let equationTrace (current:Equation) (instructions : _ list) = 
    stepTracer true string current instructions
      
let evalExpr vars x =
    replaceSymbols vars x |> Expression.FullerSimplify |> Some  

let evalExprNum vars x =
    let nums = vars |> Seq.filter (snd >> containsAnyVar >> not) 
    if Seq.isEmpty nums then None
    else let symb = replaceSymbols nums x |> Expression.FullSimplify
         if containsAnyVar symb then None else Some symb 

let evalExprVarsGen anyVar vars x =
    let v = replaceSymbols vars x |> Expression.FullSimplify  
    maybe {
        let! v' =
            Structure.recursiveFilter (Expression.isNumericOrVariable anyVar) v
        if v = v' then return v
        else return! None
    }  

let evalExprVars vars x = evalExprVarsGen false vars x     

module Vars =
    let a = symbol "a"
    let b = symbol "b"
    let c = symbol "c"
    let d = symbol "d"
    let e = symbol "e"
    let f = symbol "f"
    let g = symbol "g"
    let h = symbol "h"
    let i = symbol "i"
    let j = symbol "j"
    let k = symbol "k"
    let l = symbol "l"
    let m = symbol "m"
    let n = symbol "n"
    let o = symbol "o"
    let p = symbol "p"
    let q = symbol "q"
    let r = symbol "r"
    let s = symbol "s"
    let t = symbol "t"
    let u = symbol "u"
    let v = symbol "v"
    let w = symbol "w"
    let x = symbol "x"
    let y = symbol "y"
    let z = symbol "z"
    let x0 = symbol "x_0"
    let x1 = symbol "x_1"
    let x2 = symbol "x_2"
    let x3 = symbol "x_3"
    let v0 = symbol "v_0"
    let y0 = symbol "y_0"
    let y1 = symbol "y_1"
    let y2 = symbol "y_2"

    let A = V"A"
    let B = V"B"
    let C = V "C"
    let D = V "D"
    let M = V "M"
    let N = V "N"
    let P = V "P" 
    let Q = V "Q" 
    let T = V "T"
    let X = V "X" 
    let Y = V "Y" 
    let Z = V "Z" 

module Constants =
    let π = pi
    let pi = pi 
    let e = Constant Constant.E
   
let rational x = Expression.fromFloat x

let prob x = FunctionN(Probability, [symbol "P"; x ])
let probn s x = FunctionN(Probability, [symbol s; x ])
let condprob x param = FunctionN(Probability, [ symbol "P"; x; param ])
let probparam x param = FunctionN(Probability, [symbol "P";  x; param; 0Q ])

let expectation distr x = FunctionN(Function.Expectation, [ x; distr ])

let func f = FunctionN(Function.Func, [symbol f])
let fn f x = FunctionN(Function.Func, [symbol f;x])

let runfn fn parameters = fn |> Expression.evaluateFloat parameters |> Option.get

let makeFunc fname = fun x -> fn fname x
 
module Ops =
    let max a b = FunctionN(Function.Max, [a;b])

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
        | Power n -> " _ ^" + (Expression.toFormattedString n)
        | Function f -> string f
        | Identity -> "id"

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


    

