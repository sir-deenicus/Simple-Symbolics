module MathNet.Symbolics.Units

open Prelude.Common
open MathNet.Symbolics
open MathNet.Symbolics.Core
open MathNet.Symbolics.Utils
open MathNet.Numerics
open NumberTheory
 
type Units(q : Expression, u : Expression, ?altUnit) =
    let mutable altunit = defaultArg altUnit ("")
    new(unitname:string) = Units(1Q, symbol unitname, unitname)
    new(unitname:string, altunit:string) = Units(1Q, symbol unitname, altunit)

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
            (Expression.simplify true (a.Quantity ** b),
                Expression.simplify true (a.Unit ** b))
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
                if Expression.isRealNumber (a / b).Quantity then
                    let q, r = ((a / b).Quantity.ToFloat().Value |> smartroundEx 1)
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
        if Expression.isRealNumber t.Quantity then
            let q, r = t.Quantity.ToFloat().Value |> smartroundEx 1
            let qstr = Expression.toSciNumString r q
            if t.Unit = 1Q then qstr
            else sprintf "%s%s%s" qstr space (t.Unit.ToFormattedString())
        else
            sprintf "%s%s%s" (t.Quantity.ToFormattedString()) space
                (t.Unit.ToFormattedString())

module Desc =
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
    let charge = V"charge"
    let naira = V"naira"
    let bpound = V"gbp"
    let dollar = V"dollar"
    let density = symbol "density"

    let Names =
        set
            [   "power"
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
                 
open FSharp.Data

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
let ft =  0.3048  * meter |> setAlt "ft"
let yard = 3 * ft |> setAlt "yards"
let inches = 12 * ft |> setAlt "inches"
let au =  150Q * mega * km |> setAlt "AU" 

let liter = 1000 * cm ** 3 |> setAlt "L" 
let gallons = 3.785411784 * liter |> setAlt "gallons"
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

let lb = 0.45359237 * kg |> setAlt "lb"
let ounces = 1/16Q * lb |> setAlt "oz"

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
let bits = Units(1Q, Operators.symbol "bits", "bits")
let bytes = 8Q * bits |> setAlt "bytes"
let gigabytes = giga * bytes |> setAlt "gigabytes"
let bp = 2 * bits |> setAlt "base pairs"

let flop = Units(1Q, Operators.symbol "flop")
let exafloatops = exa * flop |> setAlt "exafloatops"
let terafloatops = tera * flop |> setAlt "terafloatops"
    
let flops = flop / sec |> setAlt "flop/s"
let gigaflops = giga * flops |> setAlt "gigaflop/s"
let teraflops = tera * flops |> setAlt "teraflop/s" 
//==============
let planck = Expression.fromFloatDouble 6.62607004e-34 * J * sec
let G = Expression.fromFloat 6.674e-11 * meter ** 3 * kg ** -1 * sec ** -2
let hbar = planck / (2 * Constants.pi)
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
    [   W, "Power"
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
        let hs = Hashset(l |> List.map (fun (u : Units) -> u.Unit))
        hs.Count = 1 || (hs.Count = 2 && hs.Contains 1Q)

    let rec replace =
        function
        | Identifier _ as v when map.ContainsKey v -> map.[v]
        | Power(x, p) -> (replace x) ** p
        | Sum l -> List.sumBy replace l
        | Product l ->
            l |> List.fold (fun p x -> p * (replace x)) (Units(1Q, 1Q))
        | FunctionN(Min as mf, l)  
        | FunctionN(Max as mf, l) as f ->
            match List.map replace l with
            | l' when (l'
                        |> List.forall (fun u -> Expression.isNumber u.Quantity)
                        && unitstest l') ->
                let minormax =
                    match mf with
                    | Min -> List.minBy
                    | Max -> List.maxBy
                    | _ -> failwith "unknown function"
                let largestorSmallest = l' |> minormax (fun u -> u.Quantity.ToFloat())
                let units = l' |> List.find (fun u -> u.Unit <> 1Q)
                Units(largestorSmallest.Quantity, units.Unit)
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
        
        
type Expression with
    static member isNumericOrVariable anyVar =
        let keep s =
            anyVar || Strings.strcontains "Var" s
            || Desc.Names.Contains s
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

    static member evalExprVarsGen anyVar vars x =
        let v = replaceSymbols vars x |> Expression.FullSimplify  
        maybe {
            let! v' =
                Structure.recursiveFilter (Expression.isNumericOrVariable anyVar) v
            if v = v' then return v
            else return! None
        }  

    static member evalExprVars vars x = Expression.evalExprVarsGen false vars x     
