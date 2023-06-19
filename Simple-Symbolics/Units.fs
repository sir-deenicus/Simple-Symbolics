module MathNet.Symbolics.Units

open Prelude.Common
open MathNet.Symbolics
open MathNet.Symbolics.Core
open MathNet.Symbolics.Utils
open MathNet.Numerics
open NumberProperties
open Prelude.Math

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
        else failwith $"Units don't match {a.Unit}, {b.Unit}"
    static member (+) (a : Units, b : int) = a + Units(ofInteger b, 1Q, "")
    static member (+) (a : int, b:Units) = Units(ofInteger a, 1Q, "") + b
  
    static member (~-) (a : Units) = (-a.Quantity, a.Unit, a.AltUnit)
    static member (-) (a : Units, b : Units) = a + -1 * b
    static member (-) (a : Units, b : int) = a - Units(ofInteger b, 1Q, "")
    static member (-) (a : int, b:Units) = Units(ofInteger a, 1Q, "") - b
    static member (*) (a : Units, b : Units) =
        Units
            (a.Quantity * b.Quantity, a.Unit * b.Unit,
                a.AltUnit + " " + b.AltUnit)

    static member (*) (a : Units, b : Expression) =
        Units(a.Quantity * b, a.Unit, a.AltUnit)

    static member (*) (a : Units, b : int) =
        Units(a.Quantity * b, a.Unit, a.AltUnit)
         
    static member (*) (a : Expression, b : Units) =
        Units(a * b.Quantity, b.Unit,
                Units.numstr a + (if b.AltUnit = "" then
                                     b.Unit.ToFormattedString()
                                  else b.AltUnit)) 

    static member (*) (a : float, b : Units) = ofFloat a * b
    
    static member (*) (a : int, b : Units) = Expression.FromInt32 a * b

    static member (*) (a : Units, b : float) =
        Units(a.Quantity * ofFloat b, a.Unit, a.AltUnit)

    static member Abs(a : Units) = Units(abs a.Quantity, a.Unit, a.AltUnit)

    static member Sqrt(x:Units) =
        Units
            (Expression.Simplify((sqrt x.Quantity) |> rm Exponents.expandRationalPower),
                Expression.Simplify((sqrt x.Unit) |> rm Exponents.expandRationalPower))

    static member Pow(a : Units, b : int) =
        Units(a.Quantity ** b, a.Unit ** b, a.AltUnit + "^" + string b)

    static member Pow(a : Units, b : Expression) =
        Units
            (Expression.simplify (a.Quantity ** b),
                Expression.simplify (a.Unit ** b))
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
                match Expression.simplify ((a / b).Quantity) with
                | IntervalF i ->
                    let struct(l,r) = i.Pair
                    let ql, rl = smartroundEx 1 l
                    let qr, rr = smartroundEx 1 r
                    let qstrl = Expression.toSciNumString rl ql
                    let qstrr = Expression.toSciNumString rr qr
                    $"[{qstrl}{space()}..{space()}{qstrr}]" 
                | _ ->
                    match Expression.toFloat (a / b).Quantity with
                    | Some f ->
                        let q, r = smartroundEx 1 f
                        Expression.toSciNumString r q
                    | None -> (Rational.simplifyNumbers 1 (Expression.simplify ((a / b).Quantity))).ToFormattedString()
            Some(sprintf "%s%s%s" qstr (space()) altunit, qstr.Length)
        else None

    static member ToUnitQuantity(a : Units, b : Units) =
        if a.Unit = b.Unit then
            Some((a / b).Quantity)
        else None

    override t.ToString() =
        match Expression.simplify t.Quantity with 
        | IntervalF i ->
            let struct(l,r) = i.Pair
            let ql, rl = smartroundEx 3 l
            let qr, rr = smartroundEx 3 r
            let qstrl = Expression.toSciNumString rl ql
            let qstrr = Expression.toSciNumString rr qr 
            let unitstr = if t.Unit = 1Q then "" else  " " + t.Unit.ToFormattedString()
            $"[{qstrl}{unitstr}..{qstrr}{unitstr}]" 
        | _ ->
            match t.Quantity.ToFloat() with
            | Some f ->
                let q, r = smartroundEx 3 f
                let qstr = Expression.toSciNumString r q
                if t.Unit = 1Q then qstr
                else sprintf "%s%s%s" qstr (space()) (if dispaltunit then altunit else t.Unit.ToFormattedString())
            | _ ->
                let qstr = (Rational.simplifyNumbers 3 (Expression.simplify t.Quantity)).ToFormattedString()
                if t.Unit = 1Q then qstr
                else sprintf "%s%s%s" qstr (space()) (if dispaltunit then altunit else t.Unit.ToFormattedString())

let setAlt alt (u : Units) =
    u.AltUnit <- alt
    u

let U = Units

let items = U"items" |> setAlt "items"
let item = items

let unitless = Units(1Q, 1Q, "")
let percent = 0.01
let pico = Expression.fromFloat64 1e-12
let nano = Expression.fromFloat64 1e-9
let micro = Expression.fromFloat64 1e-6
let milli = Expression.fromFloat64 (0.001)
let centi = Expression.FromRational(1N / 100N)
let kilo = 1000Q
let mega = 1_000_000Q
let giga = 1_000_000_000Q
let tera = 10Q ** 12
let peta = 10Q ** 15
let exa = 10Q ** 18
let zetta = 10Q ** 21
let hundred = 100Q
let thousand = kilo
let million = mega
let billion = giga
let trillion = tera
let quadrillion = peta
let quintillion = 1000 * quadrillion
let sextillion = 1000 * quintillion
let septillion = 1000 * sextillion
let octillion = 1000 * septillion
let nonillion = 1000 * octillion
let decillion = 1000 * nonillion
//----------Temperature----------
let K = Units(1Q, symbol "K", "K")
//----------Mass----------
let gram = Units(1Q, Operators.symbol "g", "g")
let kg = kilo * gram |> setAlt "kg"

let lb = 0.45359237 * kg |> setAlt "lb"
let ounces = 1/16Q * lb |> setAlt "oz"
let oz = ounces
let ton = 1000 * kg |> setAlt "metric ton"
//----------Lengths----------
let meter = Units(1Q, Operators.symbol "meters", "meter")
let km = kilo * meter |> setAlt "km"
let cm = centi * meter |> setAlt "cm"
let ft =  0.3048  * meter |> setAlt "ft"
let mile = 1.609344 * km |> setAlt "mile" 
let yard = 3 * ft |> setAlt "yards"
let inches = 1Q/12Q * ft |> setAlt "inches"
let au =  150Q * mega * km |> setAlt "AU"
let parsec =  206265 * au |> setAlt "parsec"
let mm = milli * meter |> setAlt "mm"


let liter = 1000 * cm ** 3 |> setAlt "L"
let cups = 236.588 * milli * liter |> setAlt "cups"
let floz = 0.12009504 * cups |> setAlt "floz"
let tsp = 0.0208333 * cups  |> setAlt "teaspoons"
let tbsp = 0.0625 * cups  |> setAlt "tablespoons"
let gallon = 16 * cups |> setAlt "gallons"
let ml = milli * liter |> setAlt "milli-liters"


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
let kgoe = 11.63 * kWh |> setAlt "kg of oil equivalent"
let mtoe = billion * kgoe |> setAlt "megaton of oil equivalent"

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
let humanBasePairs = 3_234_830_000Q * bp

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

//==============


//============

let usd = Units("USD")

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
        peta * flop  |> setAlt "peta flops", "computation"
        exafloatops, "computation"
        flop, "computation"
        teraops, "computation"
        peta * ops  |> setAlt "peta ops", "computation"
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
    let dollar() = if expressionFormat = InfixFormat then "$" else " \\$"
    
    let fmtString n (e : Expression) =
        let e' = Expression.simplify e
        let s = Rational.toEnglish n e'
        if s = "" then fmt (numsimplify e') else s
        
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
        fmt (numsimplify (Expression.simplify fixedunit)), shorterUnit, desc    
    
    if u.Unit = usd.Unit then 
        let amount = tounits usd u   
        let stramnt = fmtString 2 amount
        let r = dollar() + stramnt + " (Currency)" 
        r.Replace(" ", space())
    else 
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
    let u = replace vars e
    maybe {
        let! _ = u.Quantity.ToFloat()
        return u
    } 

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

let toSItring n (toUnits:Units) (u:Units) =
    let x = tounits toUnits u |> Expression.forceToFloat
    
    if x = 0. then "zero"
    elif x < 1_000_000. then 
        if n > 6 then string (log10bucket n x)
        else (log10bucket n x).ToString("N" + string n)
    else
        let p = floorf(log10f (absf x))
        let r = bucketRange 0 3. p
        sprintf "%g%s%s" (round n (x / 10. ** r)) (pow10ToSIPrefix (int r)) (toUnits.AltUnit)
          
module Physics =
    type Energy = Units 
    type Time = Units
    type Mass = Units
    type Length = Units
    type Velocity = Units
    type Acceleration = Units
    type Information = Units  

    let planck = Expression.fromFloat64 6.62607004e-34 * J * sec 
    let hbar = planck / (2 * Constants.pi)
    let speed_of_light = 299_792_458 * meter / sec
    let G = Expression.fromFloat64 6.674e-11 * meter ** 3 * kg ** -1 * sec ** -2
     
    let stefan_boltzman =
        Expression.fromFloat64 5.670367e-8 * W * meter ** -2 * K ** -4
 
    let boltzman_constant = Expression.fromFloat64 1.38064852e-23 * J / K
 
    let lightyear = speed_of_light * year
    let lightsecond = speed_of_light * sec
    let earth_radius = 6371 * km
    let earth_mass = 5.972 * 10Q**24 * kg 
    let mass_of_sun = 1.989 * 10Q**30 * kg
    let solar_system_mass = 1.0014 * mass_of_sun

    let sun_heliosphere_distance = 90 * au 
    let sun_sedna_distance = 960.78 * au
 
    let density_water = 1 * gram / cm**3
    
    let infoToThermoUnits (b: Units) = (b * boltzman_constant * ln 2Q)/bits

    ///A quantum system of energy E needs at least a time of h/4E to go from one state to an orthogonal state
    let margolusLevitinLimit (e:Energy) =
        if e.Unit <> J.Unit then failwith "Not an energy unit"
        else planck / (4 * e):Time

    let bekensteinBound (radius:Length) (energy:Energy) =  
        if radius.Unit <> meter.Unit then failwith "radius is not a unit of distance"
        if energy.Unit <> J.Unit then failwith "E is not a unit of energy"

        (2 * Operators.pi * boltzman_constant * radius * energy) / (hbar * speed_of_light) : Information
     
    ///Bremermann's limit is a limit on the maximum rate of computation that can be achieved in a self-contained system in the material universe
    let bremermannsLimit (mass:Mass) = 
        if mass.Unit <> kg.Unit then failwith "Must be a unit of mass" 
        bits * speed_of_light ** 2Q / planck * mass 

    let massToEnergy (m:Mass) = m * speed_of_light ** 2 : Energy 

    let energyToMass (e:Energy) = e / speed_of_light ** 2 : Mass

    let thermoToInfoUnits (t: Units) = t * (bits/(boltzman_constant * ln 2Q))
