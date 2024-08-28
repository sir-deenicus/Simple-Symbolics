module DiceRollerMathParser

open FParsec

type DiceExpr =
    | Dice of int * int * int
    | Mult of DiceExpr * int
    | Add of DiceExpr * DiceExpr 
    with 
    override this.ToString() = 
        let rec parseToString = function 
            | Dice(a,b, bonus) when bonus = 0 -> $"{a}d{b}"
            | Dice(a,b, bonus) -> $"{a}d{b}+{bonus}"
            | Mult(d,n) -> $"{parseToString d}*{n}"
            | Add(d1,d2) -> $"{parseToString d1}+{parseToString d2}"
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
        | Dice _ as d -> d
        | Add(d1, d2) -> 
            match evalDiceExpr d1, evalDiceExpr d2 with
            | Dice(0,0, bonus), Dice(a,b, bonus2) -> Dice(a,b, bonus + bonus2)
            | Dice(a,b, bonus), Dice(0,0, bonus2) -> Dice(a,b, bonus + bonus2)
            | Dice(a,b, bonus), Dice(c,d, bonus2) when b = d -> Dice(a+c, b, bonus + bonus2)
            | _ -> failwith "Invalid dice expression"
        | Mult(d, n) -> 
            match evalDiceExpr d with
            | Dice(a,b, bonus) -> Dice(a*n, b, bonus)
            | _ -> failwith "Invalid dice expression"
        evalDiceExpr e            
    static member InfoString = function
        | Dice(a,b, bonus) -> 
            let lower, upper = a + bonus, a * b + bonus
            let average = (lower + upper) / 2
            let bonusstr = if bonus = 0 then "" else $"+{bonus}"
            $"{a}d{b}{bonusstr}: {lower}-{upper} (avg {average})"
        | _ -> failwith "Invalid dice expression"

let dice : Parser<_,unit> = 
    pipe3 pint32 (pchar 'd') pint32 (fun a _ b -> Dice(a,b,0))

let number : Parser<_,unit> =
    pint32 |>> fun b -> Dice(0,0,b)

let diceOrNumber : Parser<DiceExpr, unit> =
    attempt dice <|> number

let ws = spaces

let multOp = ws >>. pchar '*' >>. ws >>. pint32

let factor : Parser<DiceExpr, unit> =
    diceOrNumber .>> ws .>>. (opt multOp)
    |>> function
        | (d, Some n) -> Mult(d, n)
        | (d, None) -> d

let addOp = ws >>. pchar '+' >>. ws

let expr : Parser<DiceExpr, unit> =
    chainl1 factor (addOp >>% fun a b -> Add(a, b))

let runParser input =
    match run expr input with
    | Success(result, _, _) -> Result.Ok result
    | Failure(errorMsg, _, _) -> Result.Error errorMsg