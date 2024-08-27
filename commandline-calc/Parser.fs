module Parser

open System
open Prelude.Common
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Utils
open FParsec 

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
    | Add of Expr * Expr
    | Subtract of Expr * Expr
    | Variable of Expression
    | Multiply of Expr * Expr
    | Divide of Expr * Expr
    | Power of Expr * Expr 
    | FunctionCall of string * Expr
    | Log of Expr * Expr  // base, argument

// Create parsers for the basic elements
let ws = manySatisfy (fun c -> c = ' ' || c = '\t')

let str_ws s = pstring s >>. ws

let unitPrefixes = 
    [ "giga", 1e9 * 1Q
      "mega", 1e6 * 1Q
      "kilo", 1e3 * 1Q
      "milli", 1/1000Q
      "k", 1e3 * 1Q 
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
  
let numberWithUnit = 
    pipe2 (simpleNumber .>> ws) (opt (unitExpr .>> ws))
        (fun num unit -> 
            match unit with
            | Some u -> UnitExpr(num, u)
            | None -> num)

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
 
let functionNames = ["cos"; "sin"; "tan"; "ln"; "exp"; "sqrt"]

let functionCallToExpressionFn = function
    | "cos" -> Expression.Cos
    | "sin" -> Expression.Sin
    | "tan" -> Expression.Tan
    | "ln" -> Expression.Ln
    | "exp" -> Expression.Exp
    | "sqrt" -> Expression.Sqrt
    | _ -> failwith "function not supported"

let functionParser =
    choice [
        for name in functionNames do
            yield stringCIReturn name name >>. between (str_ws "(") (str_ws ")") expr
                |>> fun arg -> FunctionCall(name, arg)
    ]

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
        attempt functionParser
        attempt logParser
        attempt parens
        attempt (numberWithUnit)
        attempt (variableWithUnit .>> ws) 
        attempt (variableParser .>> ws)
        (simpleNumber .>> ws)
    ]   

let powchoices : Parser<Expr,unit> =   
    choice [
        attempt functionParser
        attempt logParser
        attempt parens
        attempt (variableParser .>> ws)
        (simpleNumber .>> ws)
    ]   

let addOp : Parser<_, unit> = ws >>. str_ws "+" >>% Add
let subOp : Parser<_, unit> = ws >>. str_ws "-" >>% Subtract
let mulOp : Parser<_, unit> = ws >>. str_ws "*" >>% Multiply
let divOp : Parser<_, unit> = str_ws "/" >>% Divide
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
    | Success(result, _, _) -> Result.Ok result
    | Failure(errorMsg, _, _) -> Result.Error errorMsg

type ExpressionChoice =    
    | UnitExpression of Units.UnitsExpr
    | ForcedUnitExpression of Units.UnitsExpr * UnitExpr
    | PureExpression of MathNet.Symbolics.Expression

    with  
    member this.PrettyPrint() =
        let replaceOne s =
            String.replace "1.0 " "" s
        let basicUnitToPhysicsTerm = UnitExpr.BasicUnit >> unitTypesToPhysicsUnits
        match this with
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
            | Some q, _ -> $"{fmt q} {Units.simplifyUnitDesc asUnit |> replaceOne}"
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
    | ForcedUnitOutput(e, u) -> ForcedUnitExpression(evalUnitExpr e, u) 
    | e -> match evalExpr e with
            | Some e -> PureExpression e
            | None -> UnitExpression (evalUnitExpr e)
