module SimpleSymbolics.Parser

open System
open Prelude.Common
open Prelude
open MathNet.Numerics
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Utils
open FParsec
open MathNet.Symbolics.NumberProperties
open System.Collections.Generic
open System.Net.Http
open System.Text.Json

type PhysicsUnits =
    | Mass
    | Length
    | Time
    | Force
    | Energy
    | Volume
    | Information
    | Currency
    | Unitless

type UnitTypes =
    | M
    | S
    | G
    | LB
    | Ft
    | L
    | N
    | J
    | USD
    | Bits
    | Unitless
    | Custom of string 
    override this.ToString() =
        match this with
        | M -> "m"
        | S -> "s"
        | G -> "g"
        | LB -> "lb"
        | Ft -> "ft"
        | L -> "L"
        | N -> "N"
        | J -> "J"
        | USD -> "usd"
        | Bits -> "bits"
        | Unitless -> "unitless"
        | Custom s -> s

// Compound unit expression
[<RequireQualifiedAccess>]
type UnitExpr =
    | BasicUnit of UnitTypes
    | Multiply of UnitExpr * UnitExpr
    | Divide of UnitExpr * UnitExpr
    | Power of UnitExpr * int
    | Scale of Expression * UnitExpr 
    member this.Simplify() =
        let rec simplify =
            function
            | Scale(s1, Scale(s2, u)) -> Scale(s1 * s2, simplify u)
            | Scale(s, u) -> Scale(s, simplify u)
            | Multiply(u1, u2) -> Multiply(simplify u1, simplify u2)
            | Divide(u1, u2) -> Divide(simplify u1, simplify u2)
            | Power(u, n) -> Power(simplify u, n)
            | u -> u

        simplify this

// Define the expression type
type Expr = 
    | Number of Expression
    | UnitExpr of Expr * UnitExpr
    | ForcedUnitOutput of Expr * UnitExpr
    | ForcedCompoundUnitOutput of Expr * UnitExpr list 
    | DefineUnit of string
    | Add of Expr * Expr
    | Subtract of Expr * Expr
    | Variable of Expression
    | Multiply of Expr * Expr
    | Divide of Expr * Expr
    | Power of Expr * Expr
    | FunctionCall of string * Expr
    | Log of Expr * Expr
    | Round of Expr * int option              
    | FormatFloat of Expr  
    | SolveFor of Expr * Expr          
    | Differential of Expr * Expr 
    | Equation of Expr * Expr        
    | FormatToEnglish of Expr * int option   
    
/// <summary>
/// Synchronously fetches the latest exchange rates from USD and returns them
/// as a Dictionary. This function blocks until the network request completes.
/// </summary>
let getUsdExchangeRates () : Dictionary<string, float> =
    let url = "https://open.er-api.com/v6/latest/USD"
    try
        printfn "Downloading exchange rates. Please wait..."
        use client = new HttpClient()
        client.Timeout <- TimeSpan.FromSeconds(3.0) // Set timeout here
        let jsonString = client.GetStringAsync(url).Result
        use jsonDoc = JsonDocument.Parse(jsonString)
        let ratesProperty = jsonDoc.RootElement.GetProperty("rates")
        ratesProperty.Deserialize<Dictionary<string, float>>()
    with
    | ex ->
        printfn "An error occurred: %s" ex.Message
        new Dictionary<string, float>()

let depluralize (s: string) : string =
    // Basic canonicalization: widgets -> widget, meters -> meter, bytes -> byte, parties -> party
    if String.IsNullOrWhiteSpace s then s
    else
        let lower = s.ToLowerInvariant()
        if lower.EndsWith("ies") && s.Length > 3 then
            // parties -> party
            s.Substring(0, s.Length - 3) + "y"
        elif lower.EndsWith("ses") && s.Length > 3 then
            // sometimes words ending in "ses" should drop only the final 's'; keep conservative
            s.Substring(0, s.Length - 1)
        elif lower.EndsWith("s") && s.Length > 1 then
            // generic plural -> drop final 's'
            s.Substring(0, s.Length - 1)
        else s

let seenCustomUnits = Hashset()

let usdExchangeRates = getUsdExchangeRates () 
 
let tryGetCurrencyExchangeValue (target:string) =
    match usdExchangeRates.TryGetValue(target.ToUpperInvariant()) with
    | true, rate -> 1Q/Expression.fromDecimal(decimal rate)
    | _ -> Operators.undefined 


let unitPrefixes =
    [ "giga", Units.billion
      "mega", Units.million
      "kilo", 1000Q
      "milli", 1 / 1000Q
      "k", 1000Q
      "c", 1 / 100Q ]

let unitStrings =
    [ "gram", G
      "grams", G
      "meter", M
      "meters", M
      "second", S
      "seconds", S
      "liters", L
      "liter", L
      "bits", Bits
      "joules", J
      "usd", USD
      "lb", LB
      "ft", Ft
      "J", J
      "g", G
      "m", M
      "s", S
      "L", L
      "B", Bits
      "N", N ]

let unitStringsLookUp =
    unitStrings
    |> List.rev
    |> List.map (swap >> Pair.applyToLeft UnitExpr.BasicUnit)
    |> dict
    |> Dict

let basicScaledUnit =
    [ "bytes", (8Q, Bits)
      "byte", (8Q, Bits)
      "oz", (0.0625, LB)
      "inches", (1 / 12Q, Ft)
      "in", (1 / 12Q, Ft)
      "minutes", (60Q, S)
      "minute", (60Q, S)
      "hour", (3600Q, S)
      "day", (3600Q * 24, S)
      "week", (3600Q * 24 * 7, S)
      "month", (30.436875 * 24Q * 3600, S)
      "yr", (365.2425 * 24Q * 3600, S)
      "year", (365.2425 * 24Q * 3600, S)
      "ngn", (tryGetCurrencyExchangeValue "NGN", USD) 
      "gbp", (tryGetCurrencyExchangeValue "GBP", USD)
      "eur", (tryGetCurrencyExchangeValue "EUR", USD)
      "jpy", (tryGetCurrencyExchangeValue "JPY", USD)
      "mm", (1 / 1000Q, M) ] 

let allUnits =
    let postfix =
        [ for (s, u) in unitStrings -> depluralize s, UnitExpr.BasicUnit u
          for (s, (e, ut)) in basicScaledUnit -> depluralize s, UnitExpr.Scale(e, UnitExpr.BasicUnit ut) ]

    [ yield! postfix
      for (s, u) in postfix do
          for (prefix, num) in unitPrefixes do
              yield prefix + depluralize s, UnitExpr.Scale(num, u).Simplify() ]

let knownUnits = Dict.ofSeq allUnits 

let ws = manySatisfy (fun c -> c = ' ' || c = '\t')

let ws1 : Parser<string,unit> = many1Satisfy (fun c -> c = ' ' || c = '\t')

let str_ws s = pstring s >>. ws
 
let defineUnitParser =
    pstring "defunit:" >>. ws >>. many1Satisfy isLetter
    |>> fun s ->
        let key = depluralize s
        seenCustomUnits.Add key |> ignore
        DefineUnit key
        
// Parser for simple non-basic units
let basicScaledUnitParser: Parser<UnitExpr, unit> =
    choice
        [ for (str, (multiplier, unit)) in basicScaledUnit ->
              stringCIReturn str (UnitExpr.Scale(multiplier, UnitExpr.BasicUnit unit)) ]

// Parser for basic units
let basicUnitParser: Parser<UnitExpr, unit> =
    choice
        [ for (str, unit) in unitStrings do
              if str.Length = 1 then
                  yield stringReturn str (UnitExpr.BasicUnit unit)
              else
                  yield stringCIReturn str (UnitExpr.BasicUnit unit) ]

// Parser for unit prefixes
let prefixParser: Parser<Expression, unit> =
    choice (
        unitPrefixes
        |> List.map (fun (prefix, multiplier) -> stringReturn prefix multiplier)
    )

// Forward reference for unitExpr parser
let unitExpr, unitExprRef = createParserForwardedToRef<UnitExpr, unit> ()

// Parser for prefixed units
let prefixedUnit =
    pipe2 (opt prefixParser) basicUnitParser (fun prefix unitexpr ->
        match prefix with
        | Some multiplier -> UnitExpr.Scale(multiplier, unitexpr)
        | None -> unitexpr)

let prefixedScaledUnit =
    pipe2 (opt prefixParser) basicScaledUnitParser (fun prefix unitexpr ->
        match prefix with
        | Some multiplier -> UnitExpr.Scale(multiplier, unitexpr)
        | None -> unitexpr)

let customUnitParser : Parser<UnitExpr, unit> =
    many1SatisfyL isLetter "custom unit"
    >>= fun s ->
        let key = depluralize s
        if knownUnits.ContainsKey key then fail "handled by known unit parser"
        elif seenCustomUnits.Contains key then preturn (UnitExpr.BasicUnit(Custom key))
        else fail "unknown custom unit"

// Parser for unit power
let unitPower =
    pipe2
        ((attempt prefixedScaledUnit)
         <|> prefixedUnit
         <|> basicScaledUnitParser
         <|> basicUnitParser
         <|> customUnitParser)
        (opt (pstring "^" >>. pint32))
        (fun unitexpr exp ->
            match exp with
            | Some e -> UnitExpr.Power(unitexpr, e)
            | None -> unitexpr)

// Parser for basic unit or unit in parentheses
let unitTerm = unitPower <|> (between (str_ws "(") (str_ws ")") unitExpr)

// Build the unitExpr parser
do
    unitExprRef
    := let multiply = str_ws "*" >>% fun x y -> UnitExpr.Multiply(x, y) in
       let divide = str_ws "/" >>% fun x y -> UnitExpr.Divide(x, y) in
       chainl1 unitTerm (multiply <|> divide)

let expr, exprRef = createParserForwardedToRef ()  

let simpleNumber: Parser<_, unit> =
    let signParser = opt (pchar '+' <|> pchar '-')
    let integerPartParser =
        many1Satisfy isDigit
        .>>. many (pchar '_' >>. many1Satisfy isDigit)
        |>> fun (first, rest) -> first + String.concat "" rest
    let fractionalPartParser =
        opt (pchar '.' >>. many1Satisfy isDigit |>> fun digits -> "." + digits)
    let exponentPartParser =
        opt (
            (pchar 'e' <|> pchar 'E')
            >>. pipe2 (opt (pchar '+' <|> pchar '-')) (many1Satisfy isDigit)
                    (fun signOpt digits ->
                        let signStr = signOpt |> Option.map string |> Option.defaultValue ""
                        "e" + signStr + digits))
    let buildFloat (numberStr: string) =
        Number(Utils.ofFloat (Double.Parse(numberStr, System.Globalization.CultureInfo.InvariantCulture)))
    let integerNumber =
        pipe4 signParser integerPartParser fractionalPartParser exponentPartParser (fun signOpt intPart fracOpt expOpt ->
            let signStr = signOpt |> Option.map string |> Option.defaultValue ""
            let fracStr = defaultArg fracOpt ""
            let expStr = defaultArg expOpt ""
            let numberStr = signStr + intPart + fracStr + expStr
            if fracOpt.IsNone && expOpt.IsNone then
                Number(Expression.FromInteger(BigInteger.Parse(numberStr)))
            else
                buildFloat numberStr)
    let fractionalOnly =
        pipe3 signParser (pchar '.' >>. many1Satisfy isDigit) exponentPartParser (fun signOpt fracDigits expOpt ->
            let signStr = signOpt |> Option.map string |> Option.defaultValue ""
            let expStr = defaultArg expOpt ""
            let numberStr = signStr + "0." + fracDigits + expStr
            buildFloat numberStr)
    attempt fractionalOnly <|> integerNumber

let scaleFactors =
    [ "million", 1_000_000Q
      "billion", 1_000_000_000Q
      "trillion", 1_000_000_000_000Q
      "quadrillion", 1_000_000_000_000_000Q ]

let scaledNumber: Parser<_, unit> =
    let choices = List.map (fun (str, factor) -> stringCIReturn str factor) scaleFactors

    pipe2 simpleNumber (opt (ws >>. choice choices)) (fun num scaleOpt ->
        match num, scaleOpt with
        | Number n, Some scale -> Number(n * scale)
        | _ -> num)

let numberWithUnit =
    pipe2 (scaledNumber .>> ws) (opt (unitExpr .>> ws)) (fun num unit ->
        match unit with
        | Some u -> UnitExpr(num, u)
        | None -> num)
 
let simpleNumberWithCustomUnit: Parser<_, unit> =
    pipe2
        //(simpleNumber .>> spaces) // Parse a floating-point number followed by optional spaces
        (simpleNumber .>> ws)   // was .>> spaces (spaces eats newlines)
        (many1SatisfyL isLetter "custom unit") // Parse one or more letters
        (fun num unit ->
            let key = depluralize unit
            if knownUnits.ContainsKey key then
                UnitExpr(num, knownUnits[key])
            else
                // register custom unit at parse time
                seenCustomUnits.Add key |> ignore
                UnitExpr(num, UnitExpr.BasicUnit(Custom key)))

let standaloneUnitAsOne : Parser<Expr, unit> =
    // Try to interpret a bare word as an implicit 1 * unit.
    // If it isn't a known unit, fail normally so backtracking can occur.
    many1SatisfyL isLetter "unit"
    >>= fun s ->
        let key = depluralize s
        match knownUnits.TryGetValue key with
        | true, u ->
            preturn (UnitExpr(Number (Expression.FromInteger 1I), u))
        | _ when seenCustomUnits.Contains key ->
            preturn (UnitExpr(Number (Expression.FromInteger 1I), UnitExpr.BasicUnit(Custom key)))
        | _ ->
            fail "not a unit"
             
// Parser for variables
let variableParser: Parser<Expr, unit> =
    many1Satisfy2L isLetter (fun c -> isLetter c || isDigit c || c = '_') "variable"
    |>> (Expression.Symbol >> Variable)

// Parse a variable followed by an optional unit
let variableWithUnit =
    pipe2 variableParser (opt (ws >>. unitExpr)) (fun var unit ->
        match unit with
        | Some u -> UnitExpr(var, u)
        | None -> var)

let numberWithCustomUnit: Parser<_, unit> =
    pipe2
        (scaledNumber .>> ws) // Parse a floating-point number followed by optional spaces
        (many1SatisfyL isLetter "custom unit") // Parse one or more letters
        (fun num unit ->
            if knownUnits.ContainsKey(depluralize unit) then
                UnitExpr(num, knownUnits[depluralize unit])
            else
                UnitExpr(num, UnitExpr.BasicUnit(Custom(depluralize unit)))) // Combine the parsed number and unit into a tuple

let functionNames =
    [ "cos"; "sin"; "tan"; "ln"; "expand"; "exp"; "sqrt"; "simplify"; "floor"; "ceil" ]

let functionCallToExpressionFn =
    function
    | "cos" -> Expression.Cos
    | "sin" -> Expression.Sin
    | "tan" -> Expression.Tan
    | "ln" -> Expression.Ln
    | "exp" -> Expression.Exp
    | "sqrt" -> Expression.Sqrt
    | "simplify" -> Expression.simplify
    | "expand" -> Algebraic.expand
    | "floor" -> floor
    | "ceil" -> ceil
    | _ -> failwith "function not supported"

let functionParser =
    choice
        [ for name in functionNames do
              yield
                  stringCIReturn name name >>. between (str_ws "(") (str_ws ")") expr
                  |>> fun arg -> FunctionCall(name, arg) ]

let solveForParser: Parser<Expr, unit> =
    skipStringCI "solve"
    >>. ws1
    >>. skipStringCI "for"
    >>. ws1
    >>. pipe2 variableParser (ws >>. skipStringCI "in" >>. ws >>. expr) (fun v e -> SolveFor(v, e))

let solveForAltParser: Parser<Expr, unit> =
    skipStringCI "solveFor"
    >>. ws1
    >>. pipe2 variableParser (ws1 >>. expr) (fun v e -> SolveFor(v, e))

let logParser =
    pstring "log" >>. str_ws "_" >>. (variableParser <|> simpleNumber)
    .>> str_ws "("
    .>>. expr
    .>> str_ws ")"
    |>> fun (base_, arg) -> Log(base_, arg)
 
let roundParser : Parser<Expr, unit> =
    let openParen  = str_ws "("
    let closeParen = str_ws ")"
    skipStringCI "round"
    >>. openParen
    >>. pipe2
            (expr .>> ws)                                   // inner expression
            (opt (pchar ',' >>. ws >>. pint32 .>> ws))      // optional , precision
            (fun e precision -> Round(e, precision))
    .>> closeParen

// Parse parentheses with an optional unit
let parens =
    pipe2 (between (str_ws "(") (str_ws ")") expr) (opt unitExpr) (fun expr unitexpr ->
        match expr, unitexpr with
        | expr, Some u -> UnitExpr(expr, u)
        | expr, None -> expr)

let choices: Parser<Expr, unit> =
    choice
        [ attempt defineUnitParser
          attempt solveForParser
          attempt solveForAltParser
          attempt roundParser
          attempt functionParser
          attempt logParser
          attempt parens
          attempt (numberWithCustomUnit .>> ws)
          attempt (simpleNumberWithCustomUnit .>> ws)
          attempt standaloneUnitAsOne         
          attempt (variableWithUnit .>> ws)
          attempt (variableParser .>> ws)
          attempt (scaledNumber .>> ws)
          simpleNumber .>> ws ]

let powchoices: Parser<Expr, unit> =
    choice
        [ attempt functionParser
          attempt logParser
          attempt parens
          attempt (variableParser .>> ws)
          attempt (scaledNumber .>> ws)
          simpleNumber .>> ws ]

let addOp: Parser<_, unit> = ws >>. str_ws "+" >>% Add
let subOp: Parser<_, unit> = ws >>. str_ws "-" >>% Subtract
let mulOp: Parser<_, unit> = ws >>. str_ws "*" >>% Multiply
let divOp: Parser<_, unit> = ws >>. str_ws "/" >>% Divide
let powOp: Parser<_, unit> = pstring "^" >>% Power

let term =
    pipe2 choices (opt (powOp >>. powchoices)) (fun baseexpr exp ->
        match exp with
        | Some e -> Power(baseexpr, e)
        | None -> baseexpr)

// Parser for unit output specification
let unitOutputParser = str_ws ":" >>. unitExpr
  
let compoundUnitParser : Parser<UnitExpr list, unit> =
    pipe2 
        (unitExpr .>> ws1)           // first unit followed by required whitespace
        (sepBy1 unitExpr ws1)        // one or more additional units
        (fun first rest -> first::rest)

// OUTPUT MODIFIER (unit | float | eng [n])
type OutputModifier =
    | UnitMod of UnitExpr
    | CompoundUnitMod of UnitExpr list 
    | FloatMod
    | EngMod of int option

let floatModifier = skipStringCI "float" >>% FloatMod

let engModifier =
    skipStringCI "eng"
    >>. opt (ws >>. pint32)
    |>> EngMod 

let outputModifierParser : Parser<OutputModifier, unit> =
    str_ws ":" >>.
        (attempt floatModifier
         <|> attempt engModifier
         <|> attempt (compoundUnitParser |>> CompoundUnitMod)  // try compound first
         <|> (unitExpr |>> UnitMod))

let opApply op a b = op (a, b)

// Parse multiplication and division
let factor = chainl1 term (mulOp <|> divOp |>> opApply)

// Parse addition and subtraction  
do
    let arithmetic = chainl1 factor (addOp <|> subOp |>> opApply)
    let equationParser =
        pipe2 arithmetic (opt (ws >>. pchar '=' >>. ws >>. arithmetic)) (fun left rightOpt ->
            match rightOpt with
            | Some right -> Equation(left, right)
            | None -> left)

    exprRef.Value <-
        pipe2 equationParser (opt outputModifierParser) (fun e modifierOpt ->
        match modifierOpt with
        | None -> e
        | Some (UnitMod u) -> ForcedUnitOutput(e, u)
        | Some (CompoundUnitMod units) -> ForcedCompoundUnitOutput(e, units) 
        | Some FloatMod -> FormatFloat e
        | Some (EngMod n) -> FormatToEnglish(e, n)) 
  
// Parse the input
let parse (input:string) =
    if String.IsNullOrWhiteSpace (input.Trim()) then
        Result.Error "input is empty"
    else
        match run expr input with
        | Success(result, _, _) -> Result.Ok result
        | Failure(errorMsg, _, _) -> Result.Error errorMsg

// Simple line-based multi-parse: ignore blank/whitespace-only lines, parse each remaining line independently.
let mparse (input:string) =
    if String.IsNullOrWhiteSpace input then
        []
    else
        // Normalize line endings, split, drop blanks
        input.Replace("\r\n", "\n").Split('\n')
        |> Array.map (fun l -> l.TrimEnd())          // keep leading spaces if meaningful for future, trim end only
        |> Array.filter (fun l -> l.Trim() <> "")    // drop blank / whitespace-only lines
        |> Array.map (fun line ->
            match run expr line with
            | Success(result, _, _) -> result
            | Failure(msg, _, _) -> failwithf "Line parse error: %s\nLine: %s" msg line)
        |> Array.toList
          
let pow10ToPrefix n =
    let p = BigRational.floor (BigRational.log10 n)
    match p with
    | i when i = 0I -> Some ""
    | i when i = 1I -> Some "deca"
    | i when i = 2I -> Some "hecto"
    | i when i = 3I -> Some "kilo"
    | i when i = 6I -> Some "mega"
    | i when i = 9I -> Some "giga"
    | i when i = 12I -> Some "tera"
    | i when i = 15I -> Some "peta"
    | i when i = 18I -> Some "exa"
    | i when i = 21I -> Some "zetta"
    | i when i = -1I -> Some "deci"
    | i when i = -2I -> Some "centi"
    | i when i = -3I -> Some "milli"
    | i when i = -6I -> Some "micro"
    | i when i = -9I -> Some "nano"
    | i when i = -12I -> Some "pico"
    | _ -> None
 

let basicUnitTypeToUnit =
    function
    | UnitTypes.M -> Units.meter
    | UnitTypes.S -> Units.sec
    | UnitTypes.G -> Units.gram
    | UnitTypes.LB -> Units.lb
    | UnitTypes.Ft -> Units.ft
    | UnitTypes.L -> Units.liter
    | UnitTypes.N -> Units.N
    | UnitTypes.J -> Units.J
    | UnitTypes.USD -> Units.usd
    | UnitTypes.Bits -> Units.bits
    | UnitTypes.Custom s ->
        seenCustomUnits.Add(depluralize s) |> ignore
        Units.Units(depluralize s, s)
    | _ -> failwith "unit type not supported"

let rec unitExprToUnits =
    function
    | UnitExpr.BasicUnit u -> basicUnitTypeToUnit u
    | UnitExpr.Scale(multiplier, UnitExpr.BasicUnit u) -> basicUnitTypeToUnit u * multiplier
    | UnitExpr.Scale(multiplier, u) -> unitExprToUnits u * multiplier
    | UnitExpr.Multiply(u1, u2) -> unitExprToUnits u1 * unitExprToUnits u2
    | UnitExpr.Divide(u1, u2) -> unitExprToUnits u1 / unitExprToUnits u2
    | UnitExpr.Power(u, n) -> unitExprToUnits u ** n

let rec unitExprToSymbolicUnits =
    function
    | UnitExpr.BasicUnit u -> Units.UnitsExpr.Val(basicUnitTypeToUnit u)
    | UnitExpr.Scale(multiplier, UnitExpr.BasicUnit u) -> Units.UnitsExpr.Val(basicUnitTypeToUnit u * multiplier)
    | UnitExpr.Scale(multiplier, u) -> Units.UnitsExpr.Mul(Units.UnitsExpr.Const multiplier, unitExprToSymbolicUnits u)
    | UnitExpr.Multiply(u1, u2) ->
        let u1' = unitExprToSymbolicUnits u1
        let u2' = unitExprToSymbolicUnits u2
        Units.UnitsExpr.Mul(u1', u2')
    | UnitExpr.Divide(u1, u2) ->
        let u1' = unitExprToSymbolicUnits u1
        let u2' = unitExprToSymbolicUnits u2
        Units.UnitsExpr.Div(u1', u2')
    | UnitExpr.Power(u, n) ->
        let u' = unitExprToSymbolicUnits u
        Units.UnitsExpr.Pow(u', Units.UnitsExpr.Const n)

let unitTypesToPhysicsUnits =
    function
    | UnitExpr.BasicUnit M -> Length
    | UnitExpr.BasicUnit S -> Time
    | UnitExpr.BasicUnit G -> Mass
    | UnitExpr.BasicUnit L -> Length
    | UnitExpr.BasicUnit LB -> Mass
    | UnitExpr.BasicUnit Ft -> Length
    | UnitExpr.BasicUnit N -> Force
    | UnitExpr.BasicUnit J -> Energy
    | UnitExpr.BasicUnit Bits -> Information
    | UnitExpr.Power(UnitExpr.BasicUnit M, 3) -> Volume
    | UnitExpr.BasicUnit USD -> Currency
    | UnitExpr.BasicUnit Unitless -> PhysicsUnits.Unitless
    | _ -> failwith "unit type not supported"

let currencyCodeToSymbol = function 
    | "usd" -> "$"
    | "eur" -> "€"
    | "gbp" -> "£"
    | "jpy" -> "¥"
    | "ngn" -> "₦"
    | code -> code 

let scaledUnitLookUp = 
    basicScaledUnit 
    |> List.map (fun (lbl, (scale, baseunit)) -> 
        UnitExpr.Scale(scale, UnitExpr.BasicUnit baseunit), lbl) 
    |> Dict.ofSeq

scaledUnitLookUp.MergeWith(konst, unitStringsLookUp)
     
let toCompoundUnits (targetUnitExprs: UnitExpr list) (x: Units.Units) : (Expression * string) list =
    let rec iterate x converted = function
        | [] -> List.rev converted
        | unitExpr:UnitExpr::rest ->
            let targetUnit : Units.Units = unitExprToUnits (unitExpr.Simplify()) 
            let label = 
                match scaledUnitLookUp.TryGetValue(unitExpr.Simplify()) with
                | true, lbl -> lbl
                | false, _ -> 
                    // Fallback: use the UnitExpr's string representation
                    match unitExpr with
                    | UnitExpr.BasicUnit ut -> ut.ToString()
                    | UnitExpr.Scale(_, UnitExpr.BasicUnit ut) -> ut.ToString()
                    | _ -> targetUnit.AltUnit
            
            printfn "%A" targetUnit
            printfn "%A" label 

            // Calculate how many of this unit fit
            let qty = Units.tounits targetUnit x
            printfn "%A" qty
            match Expression.toRational qty with 
            | Some qtyRat -> 
                // Get the integer part (major component)
                let majorQty = BigRational.FromBigInt (BigRational.floor qtyRat) 
                let remainder = Expression.FromRational (qtyRat - majorQty) * targetUnit
                
                iterate remainder ((Expression.FromRational majorQty, label)::converted) rest
            | None -> 
                match qty with
                | Approximation (Real r) ->
                    let majorQty = Math.Floor r
                    let remainder = ofFloat (r - majorQty) * targetUnit
                    iterate remainder ((ofFloat majorQty, label)::converted) rest
                | _ -> []
    
    iterate x [] targetUnitExprs

      
type ExpressionChoice =
    | NoExpression
    | UnitExpression of Units.UnitsExpr
    | ForcedUnitExpression of Units.UnitsExpr * UnitExpr
    | ForcedUnitCompoundExpr of Units.UnitsExpr * UnitExpr list
    | PureExpression of MathNet.Symbolics.Expression
    | EquationExpression of Equations.Equation
    | EquationListExpression of Equations.Equation list
    | String of string

    member this.PrettyPrint() =
        let prettifyCompoundUnits (values: (Expression * string) list) : string =
            values
            |> List.filter (fun (qty, _) ->          
                match qty with
                | Expression.Number n when n <> 0N -> true
                | Approximation (Real r) when abs r > 1e-10 -> true
                | _ -> false)
            |> List.map (fun (qty, unitStr) ->
                let qtyStr = 
                    match qty with
                    | Expression.Number n when n.IsInteger ->
                        let i = BigRational.ToBigInt n
                        i.ToString()
                    | Expression.Number n -> fmt (Rational.round 3 n)
                    | Approximation (Real r) -> sprintf "%.3f" r
                    | _ -> fmt qty
                sprintf "%s %s" qtyStr unitStr)
            |> String.concat ", "
            
        let prettifyUnits (u: Units.Units) =
            match u.Quantity with
            | Expression.Number n when n = 1N -> fmt u.Unit
            | Expression.Number n when n = 1000N -> $"kilo{fmt u.Unit}"
            | Expression.Number n when
                n.IsInteger
                && BigInteger.Remainder(BigRational.ToBigInt(n), 8I) = 0I
                && containsVar ! "bits" u.Unit
                ->
                let rep = replaceSymbolWith ! "bytes" ! "bits" u.Unit

                match pow10ToPrefix n with
                | None -> $"{Units.simplifyUnitDesc u}"
                | Some s -> $"{s}{fmt rep}"
            | _ -> $"{Units.simplifyUnitDesc u}"

        let basicUnitToPhysicsTerm = UnitExpr.BasicUnit >> unitTypesToPhysicsUnits

        match this with
        | NoExpression -> ""
        | UnitExpression u -> Units.UnitsExpr.eval [] u |> Units.simplifyUnitDesc
        | EquationListExpression [eq]
        | EquationExpression eq -> $"{eq.ToString()}"
        | EquationListExpression eql -> 
            eql
            |> List.map (fun eq -> eq.ToString())
            |> String.concat "\n"

        | ForcedUnitCompoundExpr(unitexpr, tounitexprs) -> 
            let e = Units.UnitsExpr.eval [] unitexpr 
            let results = toCompoundUnits tounitexprs e   
            // Format as "X unit1, Y unit2, Z unit3" 
            let formatted = prettifyCompoundUnits results  
            if formatted = "" then "0"
            else formatted
        | ForcedUnitExpression(unitexpr, tounitexpr) ->
            let e = Units.UnitsExpr.eval [] unitexpr
            let asUnit = unitExprToUnits (tounitexpr.Simplify()) 
            match Units.toUnitQuantity asUnit e, tounitexpr with
            | Some q, UnitExpr.BasicUnit USD ->
                let qf = Expression.forceToFloat q
                let qfstr =  
                    if absf qf <= 0.01 then Prelude.Math.significantFiguresStr 2 qf 
                    else qf.ToString("N2", Globalization.CultureInfo.InvariantCulture)
                "$" + qfstr 
            | Some q, UnitExpr.BasicUnit u -> $"{fmt q} {u} ({unitTypesToPhysicsUnits (UnitExpr.BasicUnit u)})"
            | Some q, (UnitExpr.Scale(_, UnitExpr.BasicUnit USD) as currscale) -> 
                let qfstr = 
                    let qf = Expression.forceToFloat q  
                    if absf qf <= 0.01 then Prelude.Math.significantFiguresStr 2 qf 
                    else qf.ToString("N2", Globalization.CultureInfo.InvariantCulture)
                let currlbl = 
                    match scaledUnitLookUp.TryGetValue currscale with
                    | true, lbl -> lbl
                    | false, _ -> "usd" 
                $"""{currencyCodeToSymbol currlbl}{qfstr}"""
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit u) when n = 1 / 100Q ->
                $"{fmt q} c{u} ({basicUnitToPhysicsTerm u})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit u) when n = 1000Q ->
                $"{fmt q} k{u} ({basicUnitToPhysicsTerm u})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit u) when n = 1 / 1000Q ->
                $"{fmt q} m{u} ({basicUnitToPhysicsTerm u})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit Ft) when n = 1 / 12Q -> $"{fmt q} in (length)"
            | Some q, _ -> 
                $"{fmt (Rational.simplifyNumbers 3 q)} {prettifyUnits asUnit}"
            | _ -> "invalid unit conversion"
        | PureExpression e -> fmt e
        | String s -> s

    static member PrettyPrint(e: ExpressionChoice) = e.PrettyPrint()

let rec evalUnitExpr =
    function 
    | Number n -> Units.UnitsExpr.Const n
    | UnitExpr(Number(Expression.Number _ as n), unit) -> Units.UnitsExpr.Val(n * unitExprToUnits unit)
    | UnitExpr(expr, unit) -> Units.UnitsExpr.Mul(evalUnitExpr expr, unitExprToSymbolicUnits unit)
    | Add(a, b) -> Units.UnitsExpr.Add(evalUnitExpr a, evalUnitExpr b)
    | Subtract(a, b) -> Units.UnitsExpr.Add(evalUnitExpr a, -evalUnitExpr b)
    | Multiply(a, b) -> Units.UnitsExpr.Mul(evalUnitExpr a, evalUnitExpr b)
    | Divide(a, b) -> Units.UnitsExpr.Div(evalUnitExpr a, evalUnitExpr b)
    | Power(a, b) -> Units.UnitsExpr.Pow(evalUnitExpr a, evalUnitExpr b)
    | Variable(Identifier(Symbol s)) when knownUnits.ContainsKey s -> unitExprToSymbolicUnits knownUnits.[s]
    | Variable(Identifier(Symbol s)) when seenCustomUnits.Contains s -> Units.UnitsExpr.Val(Units.Units(s))
    | Variable(Identifier(Symbol s)) -> Units.UnitsExpr.Var s
    | Variable v -> Units.UnitsExpr.Const v
    | Round _ | FormatFloat _ | FormatToEnglish _ ->
        failwith "format/round not valid in unit expression context"
    | _ -> failwith "invalid unit expression"

let evalExpr e =
    let opfun op a b =
        match (a, b) with
        | Some a', Some b' -> Some(op a' b')
        | _ -> None

    let rec eval =
        function 
        | Number n -> Some n
        | UnitExpr _ -> None
        | Add(a, b) -> opfun (+) (eval a) (eval b)
        | Subtract(a, b) -> opfun (-) (eval a) (eval b)
        | Multiply(a, b) -> opfun (*) (eval a) (eval b)
        | Divide(a, b) -> opfun (/) (eval a) (eval b)
        | Power(a, b) -> opfun (fun a b -> a ** b) (eval a) (eval b)
        | Variable v -> Some v 
        | Log(base_, arg) -> Option.map2 (fun b a -> Expression.Log(b, a)) (eval base_) (eval arg)
        | FunctionCall(f, e) -> Option.map (functionCallToExpressionFn f) (eval e)
        | Round(e, precisionOpt) -> 
            Option.map (fun e ->
                let p = defaultArg precisionOpt 0
                Rational.round p e) (eval e) 
        | FormatFloat e ->
            Option.map (fun e -> Rational.round 0 e) (eval e)
        | _ -> None 
    eval e
    
let eval =
    function 
    | DefineUnit s ->
        seenCustomUnits.Add(depluralize s) |> ignore
        NoExpression
    | ForcedUnitOutput(e, u) -> ForcedUnitExpression(evalUnitExpr e, u)
    | ForcedCompoundUnitOutput(e, us) -> ForcedUnitCompoundExpr(evalUnitExpr e, us)
    | FormatFloat _ as e -> 
        match evalExpr e with
        | Some v ->  
            PureExpression v
        | None -> PureExpression (Expression.Symbol ("Could not format as float."))
    | FormatToEnglish(e, precisionOpt) -> 
        match evalExpr e with
        | Some expr ->
            let p = defaultArg precisionOpt 0
            String(Rational.toEnglish p expr)
        | None -> String "Could not format to English."  
    | Equation(l,r) ->
        match evalExpr l, evalExpr r with 
        | Some l', Some r' -> EquationExpression(Equations.Equation(l', r'))
        | _ -> String "Error evaluating equation."
    | SolveFor(t,Equation(eql,eqr)) -> 
        match (evalExpr t, evalExpr eql, evalExpr eqr) with 
        | Some t, Some l, Some r ->
            EquationListExpression (Solving.solveFor t (Equations.Equation(l, r)))
        | _ -> String "Error solving equation." 
    | Round(e, n) ->
        match evalExpr (Round(e, n)) with
        | Some v -> PureExpression v
        | None -> PureExpression (Expression.Symbol ("Could not round expression."))
    | e ->
        match evalExpr e with
        | Some e -> PureExpression e
        | None -> UnitExpression(evalUnitExpr e)