#I @"C:\Users\cybernetic\Code\Libs\MathNet"
#I @"C:\Users\cybernetic\Code\Libs\net4+"
#r @".\lib\net461\MathNet.Numerics.dll"
#r @".\lib\net45\MathNet.Numerics.FSharp.dll"
#r @".\fparsec\fparsecCs.dll"
#r @".\fparsec\fparsec.dll"
#r @".\MathNet.Symbolic.Ext\MathNet.Symbolic.Ext.dll"

//#r @".\symbolics\net40\mathnet.symbolics.dll"
open MathNet.Symbolics
open MathNet.Numerics
open System

type Hashset<'a> = System.Collections.Generic.HashSet<'a>

let flip f a b = f b a
let fst3 (a, _, _) = a
let pairmap f (x, y) = f x, f y
let standardSymbols = Map []
let mutable expressionFormater = Infix.format

let smartroundEx n x =
    if x > 0. && x < 1. then
        let p = log10 x
        let roundto = int(ceil -p) + n
        Math.Round(x, roundto), roundto
    else Math.Round(x, n), n

let smartround n = smartroundEx n >> fst        

let symbolString =
    function
    | Identifier(Symbol s) -> s
    | _ -> ""

module List =
    let filterMap filter map xs =
        [ for x in xs do
              if filter x then yield map x ]

module BigRational =
    open Microsoft.FSharp.Core.Operators

    ///limited by range of decimal (which is used as a less noisy alternative to floats)
    let fromFloat (f : float) =
        let df = decimal f
        if df = floor df then BigRational.FromBigInt(Numerics.BigInteger df)
        else
            let s = string (df - floor df)
            let pow10 = Numerics.BigInteger 10 ** (s.Length - 2)
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
    member t.ToFloat() = (Evaluate.evaluate standardSymbols t).RealValue
    member t.ToComplex() = (Evaluate.evaluate standardSymbols t).ComplexValue

    member t.ToInt() =
        match t with
        | Number n -> int n
        | _ -> failwith "not a number"

    member t.Rational() =
        match t with
        | Number n -> n
        | _ -> failwith "not a number"

module Expression =
    let fromFloat f = BigRational.fromFloat f |> Expression.FromRational
    let fromFloatRepeating f =
        BigRational.fromFloatRepeating f |> Expression.FromRational
    let toFloat (x : Expression) = x.ToFloat()
    let toInt (i : Expression) = i.ToInt()
    let toPlainString = Infix.format
    let toFormattedString (e : Expression) = e.ToFormattedString()
    let evaluateFloat vars expr =
        let map =
            Seq.map (fun (x, y) -> symbolString x, FloatingPoint.Real y) vars
        let symbvals = System.Collections.Generic.Dictionary(dict map)
        try Some(let v = Evaluate.evaluate symbvals expr in v.RealValue) with _ -> None

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

    let isNumber =
        function
        | Number _ -> true
        | _ -> false

    let isInteger =
        function
        | Number n when n.IsInteger -> true
        | _ -> false   
        
    let isVariable = function
        | Identifier _ -> true
        | _ -> false

let productToConstantsAndVarsGen test =
    function
    | Number _ as n -> Some(n, [])
    | Product p ->
        let nums, vars = List.partition test p
        Some(List.fold (*) 1Q nums, vars)
    | _ -> None

let productToConstantsAndVars = productToConstantsAndVarsGen Expression.isNumber

let productToIntConstantsAndVars = productToConstantsAndVarsGen Expression.isInteger

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

module Algebraic =
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
        | Product l ->
            Product
                (List.map simplifyLite
                     (collectNestedSumOrProduct Expression.isProduct l))
        | Sum l ->
            Sum
                (List.map simplifyLite
                     (collectNestedSumOrProduct Expression.isSum l))
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
            | Sum [ x ] | Product [ x ] -> simplifyLoop x
            | Product l -> List.map simplifyLoop l |> List.fold (*) 1Q
            | Sum l -> List.map simplifyLoop l |> List.sum
            | x -> x
        simplifyLoop fx |> Rational.reduce

type Expression with

    static member toRational e =
        let e' = Trigonometric.simplify e |> Algebraic.simplify true
        match e' with
        | Number(n) -> n
        | _ ->
            failwith
                (sprintf "not a number : %s => %s | %A" (e.ToFormattedString())
                     (e'.ToFormattedString()) e')

    static member fullSimplify e =
        Trigonometric.simplify e
        |> Algebraic.simplify true
        |> Algebraic.simplify true
        |> Rational.rationalize
        |> Algebraic.expand

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

open Operators

let ln = MathNet.Symbolics.Operators.ln
let arctan = MathNet.Symbolics.Operators.arctan
let symbol = symbol

module Logarithm =
    let expand =
        function
        | Function(Ln, Product l) ->
            Sum(List.map (function
                    | Power(x, n) when n = -1Q -> -ln x
                    | x -> ln x) l)
        | f -> f

    let contract =
        function
        | Sum l ->
            let logs, rest =
                List.partition (function
                    | Function(Ln, _) -> true
                    | Product [ n; Function(Ln, _) ] when n = -1Q -> true
                    | _ -> false) l

            let logs' =
                logs
                |> List.map (function
                       | Product [ n; Function(Ln, x) ] when n = -1Q -> 1 / x
                       | Function(Ln, x) -> x
                       | _ -> failwith "never")

            ln (Product logs') + Sum rest
        | f -> f

    let bringPowerOut =
        function
        | Power(x, n) -> n, x
        | f -> 1Q, f

    let powerRuleSingle =
        function
        | Function(Ln, Product l) ->
            let ns, xs = List.map bringPowerOut l |> List.unzip
            Product ns * Function(Ln, Product xs)
        | Function(Ln, Power(x, n)) -> n * Function(Ln, x)
        | f -> f

    let rec powerRule =
        function
        | Product l -> Product(List.map powerRule l)
        | Sum l -> Sum(List.map powerRule l)
        | f -> powerRuleSingle f

type Complex(r : Expression, i : Expression) =
    member __.Real = r
    member __.Imaginary = i
    member __.Conjugate = Complex(r, -i)
    member __.Magnitude = sqrt (r ** 2 + i ** 2)
    member __.ToComplex() = System.Numerics.Complex(r.ToFloat(), i.ToFloat())

    member __.Phase =
        let x, y = r.ToFloat(), i.ToFloat()
        if x > 0. then arctan (i / r)
        elif x < 0. && y >= 0. then Trigonometric.simplify (arctan (i / r) + pi)
        elif x < 0. && y < 0. then Trigonometric.simplify (arctan (i / r) - pi)
        elif x = 0. && y > 0. then pi / 2
        elif x = 0. && y < 0. then -pi / 2
        else Undefined

    static member Zero = Complex(0Q, 0Q)
    static member (~-) (a : Complex) = Complex(-a.Real, -a.Imaginary)

    member c.Pow(n : Expression, phase) =
        let r = c.Magnitude
        let angle = c.Phase
        r ** n * Complex(cos (n * (angle + phase))
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify,
                         sin (n * (angle + phase))
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify)

    static member Pow(c : Complex, n : int) = c ** (Expression.FromInt32 n)

    static member Pow(c : Complex, n : Expression) =
        let r = c.Magnitude
        let angle = c.Phase
        r ** n * Complex(cos (n * angle)
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify,
                         sin (n * angle)
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify)

    static member (+) (a : Complex, b : Complex) =
        Complex(a.Real + b.Real, a.Imaginary + b.Imaginary)
    static member (-) (a : Complex, b : Complex) =
        Complex(a.Real - b.Real, a.Imaginary - b.Imaginary)
    static member (*) (a : Complex, b : Complex) =
        Complex
            (a.Real * b.Real - a.Imaginary * b.Imaginary,
             a.Imaginary * b.Real + a.Real * b.Imaginary)
    static member (*) (a : Complex, b : Expression) =
        Complex(a.Real * b, a.Imaginary * b)
    static member (*) (a : Expression, b : Complex) =
        Complex(a * b.Real, a * b.Imaginary)
    static member (/) (a : Complex, b : Expression) =
        Complex(a.Real / b, a.Imaginary / b)

    static member (/) (a : Complex, b : Complex) =
        let conj = b.Conjugate
        (a * conj) / (b * conj).Real

    static member (/) (a : Expression, b : Complex) = (Complex a) / b
    new(r) = Complex(r, 0Q)
    override t.ToString() =
        sprintf "(%s, %s)" (t.Real.ToFormattedString())
            (t.Imaginary.ToFormattedString())

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

    member t.Evaluate(m, ?usealt) =
        Evaluate.evaluate m q,
        match usealt with
        | Some false -> u.ToFormattedString()
        | _ -> t.AltUnit

    member t.Evaluate ?usealt =
        q.ToFloat(),
        match usealt with
        | Some false -> u.ToFormattedString()
        | _ -> t.AltUnit

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

    static member (*) (a : Expression, b : Units) =
        Units(a * b.Quantity, b.Unit,
              Units.numstr a + (if b.AltUnit = "" then
                                    b.Unit.ToFormattedString()
                                else b.AltUnit))

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
            let q,r = ((a / b).Quantity.ToFloat() |> smartroundEx 1)
            let qstr = q.ToString("N" + string r) 
            Some
                (sprintf "%s %s" qstr altunit, qstr.Length)
        else None

    override t.ToString() =
        let q, r = t.Quantity.ToFloat() |> smartroundEx 1
        let qstr = q.ToString("N" + string r)
        if t.Unit = 1Q then qstr
        else sprintf "%s %s" qstr (t.Unit.ToFormattedString())

module Units =
    open System.Collections.Generic

    let (^) a b = Units(a, b)

    let setAlt alt (u : Units) =
        u.AltUnit <- alt
        u

    let unitless = Units(1Q, 1Q, "")
    let micro = Expression.fromFloat 1e-6
    let milli = Expression.fromFloat (0.001)
    let centi = Expression.FromRational(1N / 100N)
    let kilo = 1000Q
    let mega = 1_000_000Q
    let giga = 1_000_000_000Q
    let tera = 1_000_000_000_000Q
    let exa = 10Q ** 18

    let K = Units(1Q, symbol "K", "K")
    
    let gram = Units(1Q, Operators.symbol "g", "g")
    let kg = kilo * gram |> setAlt "kg"
    
    let meter = Units(1Q, Operators.symbol "meters", "meter")
    
    let sec = Units(1Q, Operators.symbol "sec", "sec")
    
    let flop = Units(1Q, Operators.symbol "flop")
    let bits = Units(1Q, Operators.symbol "bits")
    let bytes = 8Q * bits |> setAlt "bytes"
    let N = kg * meter / sec ** 2 |> setAlt "N"
    let usd = Units(1Q, symbol "\\;USD", "\\;USD")
    let exafloatops = exa * flop |> setAlt "exafloatops"
    let terafloatops = tera * flop |> setAlt "terafloatops"
    let J = kg * meter ** 2 * sec ** -2 |> setAlt "J"
    let calorie = Expression.fromFloat 4.184 * J |> setAlt "calorie"
    let km = 1000Q * meter |> setAlt "km"
    let cm = centi * meter |> setAlt "cm"
    let ft = Expression.FromRational(BigRational.fromFloat 0.3048) * meter
    let inches = 12 * ft

    let btu = Expression.FromRational(BigRational.fromFloat 1055.06) * J
    let W = (J / sec) |> setAlt "W"
    let kW = (W * 1000Q) |> setAlt "kW"
    let kJ = (J * 1000Q) |> setAlt "kJ" 
    let flops = flop / sec |> setAlt "flop/s"
    let gigaflops = giga * flops |> setAlt "gigaflop/s"
    let teraflops = tera * flops |> setAlt "teraflop/s"

    let gigabytes = giga * bytes |> setAlt "gigabytes"

    let minute = 60Q * sec |> setAlt "minute"
    let hr = 60Q * minute |> setAlt "hr"
    let days = 24Q * hr |> setAlt "days"
    let weeks = 7Q * days |> setAlt "weeks"
    let years = 52Q * weeks |> setAlt "years"
    let kWh = (kW * hr) |> setAlt "kWh"

    let differentiate (dy : Units) (dx : Units) =
        Units
            (Calculus.differentiate dy.Quantity dx.Quantity, dx.Unit / dy.Unit,
             dx.AltUnit + "/" + dy.AltUnit)

    let units =
        [ W, "Power"
          kW, "Power"
          J, "Energy"
          kJ, "Energy"
          kWh, "Energy" 
          terafloatops, "computation"
          exafloatops, "computation"
          flop, "computation"
          N, "Force"
          K, "Temperature"
          W / meter ** 2, "Energy flux"
          W / cm ** 2, "Energy flux"
          bytes, "information"
          gigabytes, "information"
          flops, "flop/s"
          gigaflops, "flop/s"
          teraflops, "flop/s"
          hr, "Time"
          years,"Time"
          weeks, "Time"
          days, "Time"
          sec, "Time"
          gram, "mass"
          kg, "mass"
          meter, "length" ]

    let simplifyUnits (u : Units) =
        let matched =
            List.filter (fun (um : Units, _) -> u.Unit = um.Unit) units
            |> List.map
                   (fun (u', t) ->
                   let s,len = Units.To(u, u') |> Option.get 
                   len, s + " (" + t + ")")
        match matched with
        | [] -> u.ToString()
        | l -> l |> List.minBy fst |> snd
         
    let rec evaluateUnits (map:IDictionary<Expression,Units>) = function
        | Identifier _ as v when map.ContainsKey v -> map.[v]
        | Power(x,p) -> (evaluateUnits map x) ** p
        | Sum l -> List.sumBy (evaluateUnits map) l
        | Product l -> l |> List.fold (fun p x -> p * (evaluateUnits map x)) (Units(1Q,1Q))    
        | f -> Units(f, 1Q)
    let tryEvaluateUnits vars e = try Some (let u = evaluateUnits (dict vars) e in u.Evaluate() ; u) with _ -> None

let rec containsVar x =
    function
    | Identifier _ as sy when sy = x -> true
    | Power(p, n) -> containsVar x n || containsVar x p
    | Function(_, fx) -> containsVar x fx
    | Product l | Sum l -> List.exists (containsVar x) l
    | _ -> false

let rec replaceSymbol r x =
    function
    | Identifier _ as var when var = x -> r
    | Power(f, n) -> Power(replaceSymbol r x f, replaceSymbol r x n)
    | Function(fn, f) -> Function(fn, replaceSymbol r x f)
    | Product l -> Product(List.map (replaceSymbol r x) l)
    | Sum l -> Sum(List.map (replaceSymbol r x) l)
    | x -> x

let rec replaceVariableSymbol replacer targetvar =
    function
    | Identifier(Symbol s) when s = targetvar -> Identifier(Symbol(replacer s))
    | Power(f, n) ->
        Power
            (replaceVariableSymbol replacer targetvar f,
             replaceVariableSymbol replacer targetvar n)
    | Function(fn, f) ->
        Function(fn, replaceVariableSymbol replacer targetvar f)
    | Product l ->
        Product(List.map (replaceVariableSymbol replacer targetvar) l)
    | Sum l -> Sum(List.map (replaceVariableSymbol replacer targetvar) l)
    | x -> x

let rec findVariablesOfExpression =
    function
    | Identifier _ as var -> [ var ]
    | Power(x, n) -> findVariablesOfExpression x @ findVariablesOfExpression n
    | Product l | Sum l -> List.collect findVariablesOfExpression l
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
        | Power _ | Function _ as expr when expr = expressionToFind ->
            replacement
        | Power(p, n) -> Power(iterReplaceIn p, iterReplaceIn n)
        | Function(f, fx) -> Function(f, iterReplaceIn fx)
        | Product l ->
            Product
                (List.map iterReplaceIn
                     (tryReplaceCompoundExpression replacement
                          expressionToFindContentSet l))
        | Sum l ->
            Sum
                (List.map iterReplaceIn
                     (tryReplaceCompoundExpression replacement
                          expressionToFindContentSet l))
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
        | _ -> false
    iterFindIn (Algebraic.simplifyLite formula)

let rec size =
    function
    | Identifier _ -> 1
    | Power(x, n) -> size x + 1 + size n
    | Product l | Sum l -> List.sumBy size l
    | Function(_, x) -> size x + 1
    | Approximation _ | Number _ -> 1
    | _ -> failwith "unimplemented compute size"

let rec depth =
    function
    | Identifier _ -> 1
    | Power(x, n) -> (max (depth x) (depth n)) + 1
    | Product l | Sum l -> 1 + (List.map depth l |> List.max)
    | Function(_, x) -> depth x + 1
    | Approximation _ | Number _ -> 1
    | _ -> failwith "unimplemented compute size"

let averageDepth =
    function
    | Sum l | Product l -> List.averageBy (depth >> float) l
    | e -> float (depth e)


module Structure =
    let exists func =
        function
        | Sum l | Product l -> List.exists func l
        | f -> func f

    let rec existsRecursive func =
        function
        | Identifier _ as i -> func i
        | Power(p, n) as pow ->
            func pow || existsRecursive func n || existsRecursive func p
        | Function(_, fx) as f -> func f || existsRecursive func fx
        | (Product l | Sum l) as prod ->
            func prod || List.exists (existsRecursive func) l
        | _ -> false

    let rec removeSymbol x =
        function
        | Identifier _ as var when var = x -> None
        | Power(f, n) ->
            match removeSymbol x f, removeSymbol x n with
            | _, None | None, _ -> None
            | Some g, Some m -> Some(Power(g, m))
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
        | x -> Some x

    let removeExpression x f =
        let placeholder = symbol "__PLACE_HOLDER__"
        let replaced = replaceExpression placeholder x f
        removeSymbol placeholder replaced

type Equation(leq : Expression, req : Expression) =

    member __.Equalities =
        [ leq, req
          req, leq ]

    override __.ToString() =
        leq.ToFormattedString() + " = " + req.ToFormattedString()

     
let (<=>) a b = Equation(a,b) 

let equals a b = Equation(a, b)

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
    let x0 = symbol "x₀"
    let x1 = symbol "x₁"
    let x2 = symbol "x₂"
    let x3 = symbol "x₃"
    let v0 = symbol "v₀"
    let y1 = symbol "y₁"
    let y2 = symbol "y₂"
    let phi = symbol "φ"
    let π = pi
    let pi = pi
