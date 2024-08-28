#r "nuget: FParsec, 1.1.1"
#I @"C:\Users\cybernetic\Jupyter-Notebooks"
#load "maths-repl.fsx"

open System
open Prelude.Common
open MathNet.Numerics
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Utils
open FParsec 
open MathNet.Symbolics.NumberProperties

let depluralize (s: string) : string =
    if s.Length > 1 && s.EndsWith("s") then s[0..s.Length - 1]
    else s

type PhysicsUnits = 
    | Mass 
    | Length
    | Time
    | Force
    | Energy
    | Volume 
    | Information 
    | Unitless
  
type UnitTypes =
    M | S | G | LB | Ft | L | N | J | Bits | Unitless | Custom of string
    with 
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
     with 
      member this.Simplify() =
        let rec simplify = function 
            | Scale(s1, Scale(s2, u)) -> Scale(s1 * s2, simplify u)
            | Scale(s, u) -> Scale(s, simplify u)
            | Multiply(u1, u2) -> Multiply(simplify u1, simplify u2)
            | Divide(u1, u2) -> Divide(simplify u1, simplify u2)
            | Power(u, n) -> Power(simplify u, n)
            | u -> u
        simplify this

let seenCustomUnits = Hashset()
let basicUnitTypeToUnit = function 
    | UnitTypes.M -> Units.meter
    | UnitTypes.S -> Units.sec 
    | UnitTypes.G -> Units.gram
    | UnitTypes.LB -> Units.lb
    | UnitTypes.Ft -> Units.ft
    | UnitTypes.L -> Units.liter
    | UnitTypes.N -> Units.N
    | UnitTypes.J -> Units.J
    | UnitTypes.Bits -> Units.bits
    | UnitTypes.Custom s -> 
        seenCustomUnits.Add (depluralize s) |> ignore; Units.Units((depluralize s), s)
    | _ -> failwith "unit type not supported"

let rec unitExprToUnits = function
    | UnitExpr.BasicUnit u -> basicUnitTypeToUnit u
    | UnitExpr.Scale(multiplier, UnitExpr.BasicUnit u) -> basicUnitTypeToUnit u * multiplier
    | UnitExpr.Scale(multiplier, u) -> unitExprToUnits u * multiplier
    | UnitExpr.Multiply(u1, u2) -> unitExprToUnits u1 * unitExprToUnits u2
    | UnitExpr.Divide(u1, u2) -> unitExprToUnits u1 / unitExprToUnits u2
    | UnitExpr.Power(u, n) -> unitExprToUnits u ** n  

let rec unitExprToSymbolicUnits = function 
    | UnitExpr.BasicUnit u -> Units.UnitsExpr.Val (basicUnitTypeToUnit u)
    | UnitExpr.Scale(multiplier, UnitExpr.BasicUnit u) -> 
        Units.UnitsExpr.Val (basicUnitTypeToUnit u * multiplier)
    | UnitExpr.Scale(multiplier, u) -> 
        Units.UnitsExpr.Mul(Units.UnitsExpr.Const multiplier, unitExprToSymbolicUnits u)
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
    
let unitTypesToPhysicsUnits = function
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
    | UnitExpr.BasicUnit Unitless -> PhysicsUnits.Unitless
    | _ -> failwith "unit type not supported"
     
// Define the expression type
type Expr =
    | Number of Expression
    | UnitExpr of Expr * UnitExpr
    | ForcedUnitOutput of Expr * UnitExpr
    | DefineUnit of string
    | Add of Expr * Expr
    | Subtract of Expr * Expr
    | Variable of Expression
    | Multiply of Expr * Expr
    | Divide of Expr * Expr
    | Power of Expr * Expr 
    | FunctionCall of string * Expr
    | Log of Expr * Expr  

let ws = manySatisfy (fun c -> c = ' ' || c = '\t')

let str_ws s = pstring s >>. ws

let unitPrefixes = 
    [ "giga", Units.billion
      "mega", Units.million
      "kilo", 1000Q
      "milli", 1/1000Q
      "k", 1000Q
      "c", 1/100Q]

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
      "lb", LB
      "ft", Ft
      "J", J
      "g", G
      "m", M
      "s", S 
      "L", L
      "B", Bits
      "N", N ]

let basicScaledUnit = 
    [ "bytes", (8Q, Bits)
      "byte", (8Q, Bits) 
      "oz", (0.0625, LB) 
      "inches", (1/12Q, Ft)
      "in", (1/12Q, Ft) 
      "minutes", (60Q, S)
      "minute", (60Q, S) 
      "hour", (3600Q, S)
      "mm", (1/1000Q, M)
    ]

let allUnits =
    let postfix = [   
        for (s,u) in unitStrings -> (depluralize s, UnitExpr.BasicUnit u)
        for (s, (e,ut)) in basicScaledUnit ->
            (depluralize s, UnitExpr.Scale(e, UnitExpr.BasicUnit ut))
    ] 
    [ 
        yield! postfix
        for (s, u) in postfix do 
            for (prefix, num) in unitPrefixes do
                yield (prefix + (depluralize s), UnitExpr.Scale(num, u).Simplify()) 
    ]

let knownUnits = Dict.ofSeq allUnits

let defineUnitParser =
    pstring "defunit:" >>. ws >>. many1Satisfy isLetter
    |>> DefineUnit

// Parser for simple non-basic units
let basicScaledUnitParser : Parser<UnitExpr, unit> =
    choice [
        for (str, (multiplier, unit)) in basicScaledUnit ->
            stringCIReturn str (UnitExpr.Scale(multiplier, UnitExpr.BasicUnit unit))
    ]

// Parser for basic units
let basicUnitParser : Parser<UnitExpr, unit> =
    choice [
        for (str, unit) in unitStrings do
            if str.Length = 1 then yield stringReturn str (UnitExpr.BasicUnit unit)
            else yield stringCIReturn str (UnitExpr.BasicUnit unit)
    ]

// Parser for unit prefixes
let prefixParser : Parser<Expression, unit> =
    choice (unitPrefixes |> List.map (fun (prefix, multiplier) -> 
        stringReturn prefix multiplier
    )) 

// Forward reference for unitExpr parser
let unitExpr, unitExprRef = createParserForwardedToRef<UnitExpr, unit>()

// Parser for prefixed units
let prefixedUnit =
    pipe2 (opt prefixParser) basicUnitParser
        (fun prefix unitexpr ->
            match prefix with
            | Some multiplier -> UnitExpr.Scale(multiplier, unitexpr)
            | None -> unitexpr)

let prefixedScaledUnit =
    pipe2 (opt prefixParser) basicScaledUnitParser
        (fun prefix unitexpr ->
            match prefix with
            | Some multiplier -> UnitExpr.Scale(multiplier, unitexpr)
            | None -> unitexpr)

// Parser for unit power
let unitPower =
    pipe2 ((attempt prefixedScaledUnit) <|> prefixedUnit <|> basicScaledUnitParser <|> basicUnitParser) (opt (pstring "^" >>. pint32))
        (fun unitexpr exp -> 
            match exp with
            | Some e -> UnitExpr.Power(unitexpr, e)
            | None -> unitexpr)

// Parser for basic unit or unit in parentheses
let unitTerm = 
    unitPower 
    <|> (between (str_ws "(") (str_ws ")") unitExpr)

// Build the unitExpr parser
do unitExprRef :=
    let multiply = str_ws "*" >>% fun x y -> UnitExpr.Multiply(x, y)
    let divide = str_ws "/" >>% fun x y -> UnitExpr.Divide(x, y)
    chainl1 unitTerm (multiply <|> divide)   

let expr, exprRef = createParserForwardedToRef()

let simpleNumber: Parser<_, unit> = 
    numberLiteral NumberLiteralOptions.DefaultFloat "number"
    |>> fun nl ->
        if nl.IsInteger then
            Expression.FromInteger (BigInteger.Parse nl.String) |> Number
        else Utils.ofFloat (Double.Parse nl.String) |> Number
  
let scaleFactors = 
    [ "million", 1_000_000Q
      "billion", 1_000_000_000Q
      "trillion", 1_000_000_000_000Q
      "quadrillion", 1_000_000_000_000_000Q
    ]

let scaledNumber: Parser<_, unit> =
    let choices = List.map (fun (str, factor) -> stringCIReturn str factor) scaleFactors
    pipe2 
        simpleNumber 
        (opt (ws >>. choice choices))
        (fun num scaleOpt ->
            match num, scaleOpt with
            | Number n, Some scale -> Number(n * scale)
            | _ -> num)

let numberWithUnit = 
    pipe2 (scaledNumber .>> ws) (opt (unitExpr .>> ws))
        (fun num unit -> 
            match unit with
            | Some u -> UnitExpr(num, u)
            | None -> num)

let simpleNumberWithCustomUnit: Parser<_, unit> =
    pipe2 
        (simpleNumber .>> spaces) // Parse a floating-point number followed by optional spaces
        (many1SatisfyL isLetter "custom unit") // Parse one or more letters
        (fun num unit -> 
            if knownUnits.ContainsKey (depluralize unit) then
                UnitExpr(num, knownUnits[depluralize unit])
            else UnitExpr(num, UnitExpr.BasicUnit (Custom (depluralize unit)))) // Combine the parsed number and unit into a tuple

// let numberWithUnit = 
//     pipe2 (simpleNumber .>> ws) (opt (unitExpr .>> ws))
//         (fun num unit -> 
//             match unit with
//             | Some u -> UnitExpr(num, u)
//             | None -> num)
// Parser for variables
let variableParser : Parser<Expr, unit> =
    many1Satisfy2L isLetter (fun c -> isLetter c || isDigit c || c = '_') "variable"
    |>> (Expression.Symbol >> Variable)

// Parse a variable followed by an optional unit
let variableWithUnit =
    pipe2 variableParser (opt (ws >>. unitExpr))
        (fun var unit ->
            match unit with
            | Some u -> UnitExpr(var, u)
            | None -> var)
 
let numberWithCustomUnit: Parser<_, unit> =
    pipe2 
        (scaledNumber .>> ws) // Parse a floating-point number followed by optional spaces
        (many1SatisfyL isLetter "custom unit") // Parse one or more letters
        (fun num unit -> 
            if knownUnits.ContainsKey (depluralize unit) then
                UnitExpr(num, knownUnits[depluralize unit])
            else UnitExpr(num, UnitExpr.BasicUnit (Custom (depluralize unit)))) // Combine the parsed number and unit into a tuple

let functionNames = ["cos"; "sin"; "tan"; "ln"; "expand"; "exp"; "sqrt"; "simplify"]

let functionCallToExpressionFn = function
    | "cos" -> Expression.Cos
    | "sin" -> Expression.Sin
    | "tan" -> Expression.Tan
    | "ln" -> Expression.Ln
    | "exp" -> Expression.Exp
    | "sqrt" -> Expression.Sqrt
    | "simplify" -> Expression.simplify
    | "expand" -> Algebraic.expand
    | _ -> failwith "function not supported"

let functionParser =
    choice [
        for name in functionNames do
            yield stringCIReturn name name >>. between (str_ws "(") (str_ws ")") expr
                |>> fun arg -> FunctionCall(name, arg)
    ]
run functionParser "expand(5)"
let logParser =
    pstring "log" >>. str_ws "_" >>. (variableParser <|> simpleNumber) .>> str_ws "(" .>>. expr .>> str_ws ")"
    |>> fun (base_, arg) -> Log(base_, arg)

// Parse parentheses with an optional unit
let parens = 
    pipe2 (between (str_ws "(") (str_ws ")") expr) (opt unitExpr)
        (fun expr unitexpr -> 
            match expr, unitexpr with
            | expr, Some u -> UnitExpr(expr, u)
            | expr, None -> expr)
 
let choices : Parser<Expr,unit> =   
    choice [
        attempt defineUnitParser
        attempt functionParser
        attempt logParser
        attempt parens
        attempt (numberWithCustomUnit .>> ws)  
        attempt (simpleNumberWithCustomUnit .>> ws)
        attempt (variableWithUnit .>> ws) 
        attempt (variableParser .>> ws)
        attempt (scaledNumber .>> ws) 
        simpleNumber .>> ws
    ] 

let powchoices : Parser<Expr,unit> =   
    choice [
        attempt functionParser
        attempt logParser
        attempt parens
        attempt (variableParser .>> ws)
        attempt (scaledNumber .>> ws)
        simpleNumber .>> ws
    ]   

let addOp : Parser<_, unit> = ws >>. str_ws "+" >>% Add
let subOp : Parser<_, unit> = ws >>. str_ws "-" >>% Subtract
let mulOp : Parser<_, unit> = ws >>. str_ws "*" >>% Multiply
let divOp : Parser<_, unit> = ws >>. str_ws "/" >>% Divide
let powOp : Parser<_, unit> = pstring "^" >>% Power

let term =  
    pipe2 
        choices 
        (opt (powOp >>. powchoices)) 
            (fun baseexpr exp -> 
                match exp with
                | Some e -> Power(baseexpr, e)
                | None -> baseexpr) 

// Parser for unit output specification
let unitOutputParser =
    str_ws ":" >>. unitExpr

let opApply op a b = op(a,b)

// Parse multiplication and division
let factor = chainl1 term (mulOp <|> divOp |>> opApply)

// Parse addition and subtraction
//do exprRef := chainl1 factor (addOp <|> subOp |>> opApply)

// Parse addition and subtraction, and optional unit output specification
do exprRef := 
    pipe2
        (chainl1 factor (addOp <|> subOp |>> opApply))
        (opt unitOutputParser)
        (fun expr unitOutput ->
            match unitOutput with
            | Some unit -> ForcedUnitOutput(expr, unit)
            | None -> expr)

let mutilineExpr = sepBy expr newline

// Parse the input
let parse input =
    match run expr input with
    | Success(result, _, _) -> result
    | Failure(errorMsg, _, _) -> failwith errorMsg

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

type ExpressionChoice =    
    | NoExpression
    | UnitExpression of Units.UnitsExpr
    | ForcedUnitExpression of Units.UnitsExpr * UnitExpr
    | PureExpression of MathNet.Symbolics.Expression
    with  
    member this.PrettyPrint() =
        let prettifyUnits (u:Units.Units) = 
            match u.Quantity with
            | Expression.Number n when n = 1N -> fmt u.Unit
            | Expression.Number n when n = 1000N -> $"kilo{fmt u.Unit}"
            | Expression.Number n when n.IsInteger && BigInteger.Remainder(BigRational.ToBigInt(n), 8I) = 0I && containsVar !"bits" u.Unit -> 
                let rep = replaceSymbolWith !"bytes" !"bits" u.Unit
                match pow10ToPrefix n with 
                | None -> $"{Units.simplifyUnitDesc u}"
                | Some s -> $"{s}{fmt rep}"
            | _ -> $"{Units.simplifyUnitDesc u}"

        let basicUnitToPhysicsTerm = UnitExpr.BasicUnit >> unitTypesToPhysicsUnits
        match this with 
        | NoExpression -> ""
        | UnitExpression u -> Units.UnitsExpr.eval [] u |> Units.simplifyUnitDesc
        | ForcedUnitExpression(unitexpr, tounitexpr) ->
            let e = Units.UnitsExpr.eval [] unitexpr
            let asUnit = unitExprToUnits (tounitexpr.Simplify()) 
            match (Units.toUnitQuantity asUnit e, tounitexpr) with 
            | Some q, UnitExpr.BasicUnit u -> $"{fmt q} {u} ({unitTypesToPhysicsUnits (UnitExpr.BasicUnit u)})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit u) when n = 1/100Q -> $"{fmt q} c{u} ({basicUnitToPhysicsTerm u})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit u) when n = 1000Q -> $"{fmt q} k{u} ({basicUnitToPhysicsTerm u})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit u) when n = 1/1000Q -> $"{fmt q} m{u} ({basicUnitToPhysicsTerm u})"
            | Some q, UnitExpr.Scale(n, UnitExpr.BasicUnit Ft) when n = 1/12Q -> $"{fmt q} in (length)"
            | Some q, _ -> 
                printfn "%A" asUnit
                printfn "%A" (prettifyUnits asUnit)
                $"{fmt (Rational.simplifyNumbers 3 q)} {prettifyUnits asUnit}"
            | _ -> "invalid unit conversion"
        | PureExpression e -> fmt e
    static member PrettyPrint (e:ExpressionChoice) = e.PrettyPrint()

let rec evalUnitExpr = function 
    | Number n -> Units.UnitsExpr.Const n
    | UnitExpr(Number (Expression.Number _ as n), unit) -> 
        Units.UnitsExpr.Val(n * unitExprToUnits unit)
    | UnitExpr(expr, unit) -> Units.UnitsExpr.Mul(evalUnitExpr expr, unitExprToSymbolicUnits unit)
    | Add(a, b) -> Units.UnitsExpr.Add(evalUnitExpr a, evalUnitExpr b)
    | Subtract(a, b) -> Units.UnitsExpr.Add(evalUnitExpr a, -evalUnitExpr b)
    | Multiply(a, b) -> Units.UnitsExpr.Mul(evalUnitExpr a, evalUnitExpr b)
    | Divide(a, b) -> Units.UnitsExpr.Div(evalUnitExpr a, evalUnitExpr b)
    | Power(a, b) -> Units.UnitsExpr.Pow(evalUnitExpr a, evalUnitExpr b)
    | Variable (Identifier (Symbol s)) when knownUnits.ContainsKey s -> unitExprToSymbolicUnits knownUnits.[s]
    | Variable (Identifier (Symbol s)) when seenCustomUnits.Contains s -> Units.UnitsExpr.Val (Units.Units (s)) 
    | Variable (Identifier (Symbol s)) -> Units.UnitsExpr.Var s
    | Variable v -> Units.UnitsExpr.Const v
    | _ -> failwith "invalid unit expression"

let evalExpr e =
    let opfun op a b =
        match (a, b) with 
        | Some a', Some b' -> Some (op a' b')
        | _ -> None
    let rec eval = 
        function 
        | Number n -> Some n 
        | UnitExpr _ -> None 
        | Add(a,b) -> opfun (+) (eval a) (eval b)
        | Subtract(a,b) -> opfun (-) (eval a) (eval b)
        | Multiply(a,b) -> opfun (*) (eval a) (eval b)
        | Divide(a,b) -> opfun (/) (eval a) (eval b)
        | Power(a,b) -> opfun (fun a b -> a ** b) (eval a) (eval b)
        | Variable v -> Some v
        | Log(base_, arg) -> Option.map2 (fun b a -> Expression.Log(b, a)) (eval base_) (eval arg)
        | FunctionCall(f, e) -> Option.map (functionCallToExpressionFn f) (eval e)
        |  _ -> None 
    eval e 

let eval = function 
    | DefineUnit s -> 
        seenCustomUnits.Add(s) |> ignore
        NoExpression
    | ForcedUnitOutput(e, u) -> ForcedUnitExpression(evalUnitExpr e, u) 
    | e -> match evalExpr e with
            | Some e -> PureExpression e
            | None -> UnitExpression (evalUnitExpr e)

let mparse input = 
    match run mutilineExpr input with
    | Success(result, _, _) -> result  
    | Failure(errorMsg, _, _) -> failwith errorMsg

mparse """20 chapters / 8 episodes"""
|> List.nth 0 |> eval |> ExpressionChoice.PrettyPrint

parse "1000 m^3 : L" |> eval |> ExpressionChoice.PrettyPrint
parse "5 m^3 * 3 kg * 2"
parse "5^3 * 2"
parse "a^2 + b^2 + c^2"  
parse "5kg*m/s^2 * 3"
parse "expand(a + b^2)"
parse "simplify(5 + 3 * 2)"
parse "sqrt(9)"
parse "16 * 6 s" |> eval |> ExpressionChoice.PrettyPrint
parse "150 kg : lb" |> eval |> ExpressionChoice.PrettyPrint
parse "5 + 3"
parse "5^(3 + 2) * 2 + 3" 
parse "2 bits" 
parse "1.6e9 param * 32 bits/param" |> eval//|> ExpressionChoice.PrettyPrint
parse "2.6 billion * 32" |> eval|> ExpressionChoice.PrettyPrint
parse "2.6 billion params * 32 bits/param" |> eval |> ExpressionChoice.PrettyPrint
parse "1.8 m : cm" |> eval |> ExpressionChoice.PrettyPrint
parse "1 kg : lb" |> eval |> ExpressionChoice.PrettyPrint
parse "1 m : ft" |> eval |> ExpressionChoice.PrettyPrint
parse "5 ft + 9 in : in" |> eval |> ExpressionChoice.PrettyPrint
parse "5 minutes / 2"
parse "cos(x + y^2)"
parse "(2 kilometer)"
parse "(2 km)"
parse "(2 kg)"
parse "(2 byte)"
parse "(2 bytes)"
parse "5m^3"
parse "log_e(c)"
parse "(5kg*m/s^2) * 3"
parse "(5 kg + 2kg) * 2"
parse "(5 meter + 2 m) + (1 km)"
parse "5 kg + 2kg * 2" |> eval |> ExpressionChoice.PrettyPrint
parse "5+1*2"
parse "5^3"
parse "a^2*b*c"
parse "a+2+c"
parse "a+b"
parse "a^b"
parse "a kg+b kg+c"    
parse "a byte+b byte+c"    
parse "a kg + b kg * c" |> eval// |> ExpressionChoice.PrettyPrint   
parse "a byte + b byte * c"  
parse "a + b"
parse "(2 megajoules)"
parse "2 gigabytes + 1 kilobytes" |> eval |> ExpressionChoice.PrettyPrint

parse "80 kilobytes/s : kilobits/s" |> eval |> ExpressionChoice.PrettyPrint
 
//let choices2 = (attempt parens <|> attempt numberWithUnit <|> (attempt variableWithUnit <|> attempt variableParser) <|> (pfloat |>> Number)) 
// let term =  
//     pipe2   (attempt parens <|> attempt numberWithUnit <|> (pfloat |>> Number)) 
//             (opt (powOp >>. (attempt parens <|> attempt numberWithUnit <|> (pfloat |>> Number)))) 
//             (fun baseexpr exp -> 
//                 match exp with
//                 | Some e -> Power(baseexpr, e)
//                 | None -> baseexpr)
 
//type Operator = Add | Subtract | Multiply | Divide | Power

// let factor =
//     let unitFactor = chainl1 term (mulOp <|> divOp |>> fun op a b -> BinOp(a, op, b))
//     let multFactor = pipe2 term (opt (mulOp >>. term)) (fun a op -> 
//         match op with
//         | Some b -> BinOp(a, Multiply, b)
//         | None -> a)
//     let divFactor = pipe2 term (opt (divOp >>. term)) (fun a op ->
//         match op with
//         | Some b -> BinOp(a, Divide, b)
//         | None -> a)
//     multFactor <|> divFactor <|> unitFactor

//let parens = between (str_ws "(") (str_ws ")") expr
// Parse a term (number with unit or parenthesized expression)
//let term = attempt numberWithUnit <|> parens <|> (pfloat |>> Number)
// Parse a term (number with unit, parenthesized expression, or plain number)
//let term = attempt parens <|> attempt numberWithUnit <|> (pfloat |>> Number)

// let unitParser : Parser<UnitOfMeasure, unit> =
//     choice [
//         stringCIReturn "kg" Kg
//         stringCIReturn "g" G
//         stringCIReturn "m" M
//         stringCIReturn "ft" Ft
//     ] .>> ws
//    <|> preturn NoUnit

// Create a forward reference for the expression parser
// let expr, exprRef : Parser<Expr, unit> * Parser<Expr, unit>ref = createParserForwardedToRef() 

// Parse a number with an optional unit
// let numberWithUnit = 
//     pipe2 (pfloat .>> ws) (opt unitParser)
//         (fun num unit -> 
//             match unit with
//             | Some u -> UnitExpr(Number num, u)
//             | None -> Number num)

// Parse parentheses with an optional unit
// let parens = 
//     pipe2 (between (str_ws "(") (str_ws ")") expr) (opt unitParser)
//         (fun expr unit -> 
//             match unit with
//             | Some u -> UnitExpr(expr, u)
//             | None -> expr)

// Parse parentheses with an optional compound unit
// let parens = 
//     pipe2 (between (str_ws "(") (str_ws ")") expr) (opt unitExpr)
//         (fun expr unit -> 
//             match expr, unit with
//                | Number n, Some u -> UnitNumber(n, u)
//          | _ -> expr)  // If it's not a simple number, we ignore the unit (this could be handled differently)

// Parse parentheses
// let parens : Parser<_, unit> = between (str_ws "(") (str_ws ")") expr

// Parse a term (number or parenthesized expression)
//let term : Parser<_, unit> = float_ws |>> Number <|> parens

// let term : Parser<Expr, unit> = 
//     (pipe2 float_ws (opt unitParser)
//         (fun num unittype -> Number(num, defaultArg unittype NoUnit)))
//     <|> parens

// Parse multiplication and division
// let factor = chainl1 term (mulOp <|> divOp |>> fun op a b -> BinOp(a, op, b))

// Parse addition and subtraction
// exprRef := chainl1 factor (addOp <|> subOp |>> fun op a b -> BinOp(a, op, b))
