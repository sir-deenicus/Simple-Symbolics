module MathNet.Symbolics.Units

open Prelude.Common
open MathNet.Symbolics
open MathNet.Symbolics.Core
open MathNet.Symbolics.Utils
open MathNet.Numerics
open NumberProperties
open NumberProperties

type Units(q : Expression, u : Expression, ?altUnit, ?dispAltUnit) =
    let mutable altunit = defaultArg altUnit ("")
    let mutable dispaltunit = defaultArg dispAltUnit false
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

    member __.DisplayWithAltUnit
        with get () = dispaltunit
        and  set t = dispaltunit <- t

    member t.EvaluateQuantity(m) =
        Expression.evaluateFloat m q

    member t.EvaluateQuantity () = q.ToFloat()

    member __.GetAltString() = sprintf "%s %s" (u.ToFormattedString()) altunit

    member __.Reciprocal (u:Units) =
        Units(Rational.reciprocal u.Quantity, Rational.reciprocal u.Unit)

    member u.ToQuantity u2 = Units.ToUnitQuantity(u, u2)

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
        Units(a.Quantity * ofFloat b, a.Unit, a.AltUnit)

    static member (*) (a : float, b : Units) = ofFloat a * b

    static member (*) (a : Expression, b : Units) =
        Units(a * b.Quantity, b.Unit,
                Units.numstr a + (if b.AltUnit = "" then
                                     b.Unit.ToFormattedString()
                                  else b.AltUnit))

    static member Abs(a : Units) = Units(abs a.Quantity, a.Unit, a.AltUnit)

    static member Sqrt(x:Units) =
        Units
            (Expression.Simplify((sqrt x.Quantity) |> rm Exponents.expandRationalPower),
                Expression.Simplify((sqrt x.Unit) |> rm Exponents.expandRationalPower))

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
                match Expression.toFloat (a / b).Quantity with
                | Some f ->
                    let q, r = smartroundEx 1 f
                    Expression.toSciNumString r q
                | None -> (Rational.simplifyNumbers 1 (a / b).Quantity).ToFormattedString()
            Some(sprintf "%s%s%s" qstr (space()) altunit, qstr.Length)
        else None

    static member ToUnitQuantity(a : Units, b : Units) =
        if a.Unit = b.Unit then
            Some((a / b).Quantity)
        else None

    override t.ToString() =
        match t.Quantity.ToFloat() with
        | Some f ->
            let q, r = smartroundEx 1 f
            let qstr = Expression.toSciNumString r q
            if t.Unit = 1Q then qstr
            else sprintf "%s%s%s" qstr (space()) (if dispaltunit then altunit else t.Unit.ToFormattedString())
        | _ ->
            sprintf "%s%s%s" ((Rational.simplifyNumbers 1 t.Quantity).ToFormattedString()) (space())
                (if dispaltunit then altunit else t.Unit.ToFormattedString())

let setAlt alt (u : Units) =
    u.AltUnit <- alt
    u 

let U = Units

let unitless = Units(1Q, 1Q, "")
let percent = 0.01
let pico = Expression.fromFloat 1e-12
let nano = Expression.fromFloat 1e-9
let micro = Expression.fromFloat 1e-6
let milli = Expression.fromFloat (0.001)
let centi = Expression.FromRational(1N / 100N)
let kilo = 1000Q
let mega = 1_000_000Q
let giga = 1_000_000_000Q
let tera = 10Q ** 12
let peta = 10Q ** 15
let exa = 10Q ** 18
let hundred = 100Q
let thousand = kilo
let million = mega
let billion = giga
let trillion = tera
let quadrillion = peta
let quintillion = 1000 * quadrillion
let sextillion = 1000 * quintillion
//----------Temperature----------
let K = Units(1Q, symbol "K", "K")
//----------Mass----------
let gram = Units(1Q, Operators.symbol "g", "g")
let kg = kilo * gram |> setAlt "kg"

let lb = 0.45359237 * kg |> setAlt "lb"
let ounces = 1/16Q * lb |> setAlt "oz"
let oz = ounces
//----------Lengths----------
let meter = Units(1Q, Operators.symbol "meters", "meter")
let km = kilo * meter |> setAlt "km"
let cm = centi * meter |> setAlt "cm"
let ft =  0.3048  * meter |> setAlt "ft"
let mile = 1.609344 * km
let yard = 3 * ft |> setAlt "yards"
let inches = 1Q/12Q * ft |> setAlt "inches"
let au =  150Q * mega * km |> setAlt "AU"
let parsec =  206265 * au |> setAlt "parsec"

let liter = 1000 * cm ** 3 |> setAlt "L"
let cups = 236.588 * milli * liter |> setAlt "cups"
let tsp = 0.0208333 * cups  |> setAlt "teaspoons"
let tbsp = 0.0625 * cups  |> setAlt "tablespoons"
let gallon = 16 * cups |> setAlt "gallons"
let ml = milli * liter |> setAlt "milli-liters"

let density_water = 1 * gram / cm**3

//----------Time
let sec = Units(1Q, Operators.symbol "sec", "sec")
let minute = 60Q * sec |> setAlt "minute"
let minutes = minute |> setAlt "minutes"
let hr = 60Q * minute |> setAlt "hr"
let hrs = hr |> setAlt "hrs"
let days = 24Q * hr |> setAlt "days"
let day = days |> setAlt "day"
let month = 30.4167 * day |> setAlt "month"
let months = month |> setAlt "months"
let weeks = 7Q * days |> setAlt "weeks"
let years = 365.24 * days |> setAlt "years"
let year = years |> setAlt "year"
//----------
let N = kg * meter / sec ** 2 |> setAlt "N"

let J = kg * meter ** 2 * sec ** -2 |> setAlt "J"
let kJ = (J * 1000Q) |> setAlt "kJ"
let calorie = 4.184 * J |> setAlt "calorie"
let food_calorie = kilo * calorie |> setAlt "food calorie"
let btu = 1055.06 * J  |> setAlt "btu"
let eV = 1.602176634e-19 * J |> setAlt "eV"

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

let flop = Units(1Q, Operators.symbol "flop", "flop")
let exafloatops = exa * flop |> setAlt "exa flops"
let terafloatops = tera * flop |> setAlt "tera flops"

let flops = flop / sec |> setAlt "flop/s"
let gigaflops = giga * flops |> setAlt "gigaflop/s"
let teraflops = tera * flops |> setAlt "teraflop/s"

let ops = Units(1Q, Operators.symbol "op", "op")
let exaops = exa * ops |> setAlt "exa-ops"
let teraops = tera * ops |> setAlt "tera-ops"

let opspersec = flop / sec |> setAlt "ops/s"
let gigaopspersec = giga * flops |> setAlt "gigaops/s"
let teraopspersec = tera * flops |> setAlt "teraops/s"
//==============
let planck = Expression.fromFloatDouble 6.62607004e-34 * J * sec
let G = Expression.fromFloat 6.674e-11 * meter ** 3 * kg ** -1 * sec ** -2
let hbar = planck / (2 * Constants.pi)
let speed_of_light = 299_792_458 * meter / sec
let mass_of_sun = 1.989 * 10Q**30 * kg
let stefan_boltzman =
    Expression.fromFloat 5.670367e-8 * W * meter ** -2 * K ** -4
let boltzman_constant = Expression.fromFloat 1.38064852e-23 * J / K
//==============

let lightyear = speed_of_light * year
let lightsecond = speed_of_light * sec

//=============
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
        peta * flop  |> setAlt "peta-ops", "computation"
        exafloatops, "computation"
        flop, "computation"
        teraops, "computation"
        peta * ops  |> setAlt "peta-ops", "computation"
        exaops, "computation"
        ops, "computation"
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
        peta * flops |> setAlt "petaflop/s", "flop/s"
        opspersec, "ops/s"
        gigaopspersec, "ops/s"
        teraopspersec, "ops/s"
        peta * opspersec |> setAlt "peta-ops/s", "ops/s"
        ml, "volume"
        liter, "volume"
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

let unitsmap = Dict.ofSeq (List.map swap units)

let unitsName = Dict.ofSeq (List.map (fun (u:Units,s) -> u.Unit, s) units)

let trylookupUnit e =
    match unitsName.tryFind e with
    | None ->
        match unitsName.tryFind (1 / e) with
        | None -> "" | Some s -> "Inverse" + space() + s
    | Some s -> s

let mostSimilarUnit (unitExpr : Units) =
    [ for (u, s) in units do
          let unitAdj = unitExpr.Unit * Rational.reciprocal u.Unit
          yield "*" + " " + s, unitAdj, u, sprintf "%s * %s" (fmt unitAdj) (u.AltUnit),
                Structure.size (unitAdj)
          let unitAdj2 = unitExpr.Unit * u.Unit
          yield "/" + " " + s, unitAdj2, u, sprintf "%s/%s" (fmt unitAdj2) (u.AltUnit),
                Structure.size (unitAdj2) ]
    |> List.groupBy fst5
    |> List.map (snd >> List.minBy (fourth5 >> String.length))
    |> List.sortBy fifth

let toUnitQuantity (b : Units) (a : Units) =
    if a.Unit = b.Unit then
        Some((a / b).Quantity)
    else None

let toUnitQuantityValue (a : Units) (b : Units) =
    toUnitQuantity a b |> Option.get

let getUnitQuantity (u:Units) = u.Quantity

let tounits =  toUnitQuantityValue

let toUnitsN units x =
    let rec iterate x converted = function
        | [] -> List.rev converted
        | u::us ->
            let M = tounits u x
            let f = Expression.forceToFloat M

            let majorQ = ofFloat (floorf f)
            let minor = ofFloat (f - floorf f) * u

            iterate minor ((majorQ, u.AltUnit)::converted) us
    iterate x [] units

let toUnits2 major minor x = toUnitsN [major;minor] x

let simplifyUnitDescAux numsimplify (u : Units) =
    let trysimplify (u : Units) =
        let uop, adjustedunit, adjustingunit, shorterUnit, _ =
            mostSimilarUnit u |> List.head

        let fixedunit =
            if uop.[0] = '*' then
                toUnitQuantityValue (Units(1Q, adjustedunit) * adjustingunit) u
            else toUnitQuantityValue (Units(1Q, adjustedunit) / adjustingunit) u

        let adjdesc = trylookupUnit adjustedunit

        let desc =
            if adjdesc = "" then ""
            else space() + "(" + adjdesc + space() + uop + ")"
        fmt (numsimplify fixedunit), shorterUnit, desc

    let matched =
        List.filter (fun (um : Units, _) -> u.Unit = um.Unit) units
        |> List.map (fun (u', t) ->
               let s, len = Units.To(u, u') |> Option.get
               len, s + space() + "(" + t + ")")

    match matched with
    | [] ->
        if Seq.forall unitsName.ContainsKey (Expression.findVariables u.Unit) then
            let basic = u.ToString()
            let chunit, units, desc = trysimplify u
            if basic.Length <= (chunit + units).Length then basic
            else chunit + space() + units + desc
        else u.ToString()
    | l -> l |> List.minBy fst |> snd

let simplifyUnitDesc (u : Units) = simplifyUnitDescAux (Rational.simplifyNumbers 3) u

let rec replace (defs : seq<Expression * Units>) e =
    let map = dict defs

    let unitstest l =
        let hs = Hashset(l |> List.map (fun (u : Units) -> u.Unit))
        hs.Count = 1 || (hs.Count = 2 && hs.Contains 1Q)

    let rec replaceLoop =
        function
        | Identifier _ as v when map.ContainsKey v -> map.[v]
        | Power(x, p) -> (replaceLoop x) ** p
        | Sum l -> List.sumBy replaceLoop l
        | Product l ->
            l |> List.fold (fun p x -> p * (replaceLoop x)) (Units(1Q, 1Q))
        | FunctionN(Min as mf, l)
        | FunctionN(Max as mf, l) as f ->
            match List.map replaceLoop l with
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
    replaceLoop e

let tryreplace vars e =
    try
        let u = replace vars e
        u.EvaluateQuantity() |> ignore
        Some u
    with _ -> None

let map f (q:Units) =
    Units(f q.Quantity, q.Unit )

let toCelsius (u:Units) =
    if u.Unit = Vars.K then
        Some(u.Quantity - 273.15)
    else None

let inline celsiusToFahrenheit c =
    Expression.toFloat(c * 9Q/5Q + 32Q)

let fahrenheitToCelsius f =
    5Q/9Q * (f - 32Q) |> Expression.toFloat

let fromCelsius (x:float) =
    (x + 273.15) * K

let MargolusLevitinLimit (e:Units) =
    if e.Unit <> J.Unit then failwith "Not an energy unit"
    else planck / (4 * e)
