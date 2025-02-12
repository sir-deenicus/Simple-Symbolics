module DiceRollerMathParser

open FParsec
open Hansei.TreeSearch.LazyList 
open Hansei.FSharpx.Collections

let diceParams rollsUpper take nobonus
    (lowerBound:int option, upperBound:int option, averageBound:int option) = 
    let rollsupper = defaultArg rollsUpper 20
    search {
        let! dice = choices [2;3;4;6;8;10;12]
        let! roll = choices [1..rollsupper]
        let! bonus = if nobonus then exactly 0 else choices [0..rollsupper] 
        
        let lower, upper = roll + bonus, roll * dice + bonus
        let average = (lower + upper) / 2
        match (lowerBound, upperBound, averageBound) with
        | Some lb, Some ub, _ -> 
            do! guard (lower = lb && upper = ub)
            return (dice, roll, bonus, average, $"{roll}d{dice}+{bonus}")
        | _, Some ub, Some ab -> 
            do! guard (upper = ub && average = ab)
            return (dice, roll, bonus, average, $"{roll}d{dice}+{bonus}")
        | Some lb, _, Some ab ->
            do! guard (lower = lb && average = ab)
            return (dice, roll, bonus, average, $"{roll}d{dice}+{bonus}")
        | _, _, Some ab -> 
            do! guard (average = ab)
            return (dice, roll, bonus, average, $"{roll}d{dice}+{bonus}")
        | _, _, _ -> return! fail()
    }
    |> LazyList.takeOrMax take
    |> LazyList.toList

open System.Text.RegularExpressions

let (|RangePattern|_|) (input: string) =
    let m = Regex.Match(input, @"^(\d+)-(\d+)$")
    if m.Success then
        Some (int m.Groups.[1].Value, int m.Groups.[2].Value)
    else
        None
        
let (|AveragePattern|_|) (input: string) =
    let m = Regex.Match(input, @"^avg (\d+)$")
    if m.Success then
        Some (int m.Groups.[1].Value)
    else
        None

let (|MinAveragePattern|_|) (input: string) =
    let m = Regex.Match(input, @"^(?:min (\d+), avg (\d+))|(?:avg (\d+), min (\d+))$")
    if m.Success then
        let minVal = if m.Groups.[1].Success then int m.Groups.[1].Value else int m.Groups.[4].Value
        let avgVal = if m.Groups.[2].Success then int m.Groups.[2].Value else int m.Groups.[3].Value
        Some (minVal, avgVal)
    else
        None

let (|MaxAveragePattern|_|) (input: string) =
    let m = Regex.Match(input, @"^(?:max (\d+), avg (\d+))|(?:avg (\d+), max (\d+))$")
    if m.Success then
        let maxVal = if m.Groups.[1].Success then int m.Groups.[1].Value else int m.Groups.[4].Value
        let avgVal = if m.Groups.[2].Success then int m.Groups.[2].Value else int m.Groups.[3].Value
        Some (maxVal, avgVal)
    else
        None
        
let parseDiceParamsInput (input: string) =
    match input with
    | RangePattern (lb, ub) -> (Some lb, Some ub, None)
    | AveragePattern avg -> (None, None, Some avg)
    | MinAveragePattern (lb, avg) -> (Some lb, None, Some avg)
    | MaxAveragePattern (ub, avg) -> (None, Some ub, Some avg)
    | _ -> (None, None, None)

type DiceExpr =
    | Dice of int * int * int
    | Mult of DiceExpr * int
    | Add of DiceExpr * DiceExpr 
    | Sub of DiceExpr * int
    with 
    override this.ToString() = 
        let rec parseToString = function 
            | Dice(a,b, bonus) when bonus = 0 -> $"{a}d{b}"
            | Dice(a,b, bonus) -> $"{a}d{b}+{bonus}"
            | Mult(d,n) -> $"{parseToString d}*{n}"
            | Add(d1,d2) -> $"{parseToString d1}+{parseToString d2}"
            | Sub(d,n) -> $"{parseToString d}-{n}"
        parseToString this
    member this.ToPair = function 
        | Dice(a,b, _) -> (a,b)
        | _ -> failwith "Invalid dice expression"
    member this.ToTriple = function 
        | Dice(a,b, bonus) -> (a,b, bonus)
        | _ -> failwith "Invalid dice expression"
    member this.ToRangePair = function
        | Dice(a,b, bonus) -> (a + bonus, a * b + bonus)
        | _ -> failwith "Invalid dice expression" 
    member this.Eval() = DiceExpr.EvalDiceExpr this            
    static member EvalDiceExpr e = 
        let rec evalDiceExpr = function 
        | Dice _ as d -> Result.Ok d
        | Add(Sub(d, n), d2) -> 
            match evalDiceExpr d, evalDiceExpr d2 with
            | Result.Ok d, Result.Ok d2 -> 
                Result.Ok (Add(Sub(d, n), d2))
            | _ -> Result.Error "Invalid dice expression" 
        | Add(d1, d2) -> 
            match evalDiceExpr d1, evalDiceExpr d2 with
            | Result.Ok (Dice(0,0, bonus)), Result.Ok (Dice(a,b, bonus2)) -> Result.Ok (Dice(a,b, bonus + bonus2))
            | Result.Ok (Dice(a,b, bonus)), Result.Ok (Dice(0,0, bonus2)) -> Result.Ok (Dice(a,b, bonus + bonus2))
            | Result.Ok (Dice(a,b, bonus)), Result.Ok (Dice(c,d, bonus2)) when b = d -> 
                Result.Ok (Dice(a+c, b, bonus + bonus2))
            | Result.Ok (Dice(a,b, bonus)), Result.Ok (Dice(c,d, bonus2)) ->
                Result.Ok (Add(Dice(a,b, bonus), Dice(c,d, bonus2)))
            | _ -> Result.Error "Invalid dice expression"
        | Mult(d, n) -> 
            match evalDiceExpr d with
            | Result.Ok (Dice(a,b, bonus)) -> Result.Ok (Dice(a*n, b, n*bonus))
            | _ -> Result.Error "Invalid dice expression"
        | Sub(d, n) ->  // Add this case
            match evalDiceExpr d with
            | Result.Ok (Dice(a,b, bonus)) -> Result.Ok (Dice(a, b, bonus - n))
            | _ -> Result.Error "Invalid dice expression"
        evalDiceExpr e

    static member InfoString = function
        | Add(Dice(a,b, bonus), Dice(c,d, bonus2)) -> 
            let lower1, upper1 = (a + bonus), (a * b + bonus)
            let lower2, upper2 = c + bonus2, c * d + bonus2
            let lower, upper = lower1 + lower2, upper1 + upper2
            let average = (lower + upper) / 2
            $"({a}d{b}+{bonus}) + {c}d{d}+{bonus2}: {max 0 lower}-{max 0 upper} (avg {max 0 average})"
        | Add(Sub(d, n), d2) -> 
            let d1 = d.Eval()
            let d2 = d2.Eval()
            match d1, d2 with
            | Result.Ok(Dice(a,b, bonus)), Result.Ok(Dice(c,d, bonus2)) -> 
                let lower1, upper1 = (a + bonus) - n, (a * b + bonus) - n
                let lower2, upper2 = c + bonus2, c * d + bonus2
                let lower, upper = lower1 + lower2, upper1 + upper2
                let average = (lower + upper) / 2
                $"({a}d{b}-{n}) + {c}d{d}: {max 0 lower}-{max 0 upper} (avg {max 0 average})"
            | _ -> failwith "Invalid dice expression"
        | Dice(a,b, bonus) -> 
            let lower, upper = a + bonus, a * b + bonus
            let average = (lower + upper) / 2
            let bonusstr = if bonus = 0 then "" else $"+{bonus}"
            $"{a}d{b}{bonusstr}: {max 0 lower}-{max 0 upper} (avg {max 0 average})"
        | _ -> failwith "Invalid dice expression"

let ws = spaces

let str_ws s = pstring s >>. ws

let dice : Parser<_,unit> = 
    pipe3 pint32 (pchar 'd') pint32 (fun a _ b -> Dice(a,b,0))

let number : Parser<_,unit> =
    pint32 |>> fun b -> Dice(0,0,b)

let diceOrNumber : Parser<DiceExpr, unit> =
    attempt (dice .>> ws) <|> (number .>> ws)

let multOp = ws >>. pchar '*' >>. ws >>. pint32 

let expr, exprRef = createParserForwardedToRef()

let parens = between (str_ws "(") (str_ws ")") expr

// Add new parser for stats query
let statsQuery = 
    pstring "\\s" >>. restOfLine true 
    |>> (fun s ->  
        let bounds = parseDiceParamsInput (s.Trim()) 
        match diceParams None 20 false bounds with
        | [] ->  
            printfn "No dice combination found"
            Dice(0,0,0)
        | (dice,rolls,bonus,_,_)::_ -> Dice(rolls,dice,bonus))

// Modify factor to include statsQuery
let factor = parens <|> statsQuery <|> diceOrNumber 

let term = 
    factor .>>. opt multOp
    |>> function
        | (d, Some n) -> Mult(d, n)
        | (d, None) -> d

do exprRef :=
    let addOp = ws >>. str_ws "+" >>% fun a b -> Add(a, b)
    let subOp = ws >>. str_ws "-" >>% fun a b -> 
        match b with
        | Dice(0,0,n) -> Sub(a, n)
        | _ -> failwith "Subtraction requires a number"
    chainl1 term (attempt addOp <|> subOp)

let runParser input =
    match run expr input with
    | Success(result, _, _) -> Result.Ok result
    | Failure(errorMsg, _, _) -> Result.Error errorMsg