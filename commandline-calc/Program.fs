open System
open SimpleSymbolics.Parser
open System.Collections.Generic

let previousMsgs = ResizeArray([""])

let convertSuperscripts (input: string) =
    let superscripts = "⁰¹²³⁴⁵⁶⁷⁸⁹"
    input.ToCharArray()
    |> Array.map (fun c ->
        match superscripts.IndexOf(c) with
        | -1 -> c.ToString()
        | n -> "^" + n.ToString())
    |> String.concat ""

let rec getInputWithHistory prefillmsg pos (prevMsg:string) =
    let mutable currentPos = pos
    let mutable currentInput = if prefillmsg then prevMsg else ""
    let mutable cursorIndex = currentInput.Length
    let promptLen = $"In [{pos+1}]: ".Length
    
    let writeInput() =
        Console.SetCursorPosition(0, Console.CursorTop)
        Console.Write(new string(' ', Console.WindowWidth - 1))
        Console.SetCursorPosition(0, Console.CursorTop)
        Console.Write($"In [{pos+1}]: " + currentInput)
        Console.SetCursorPosition(cursorIndex + promptLen, Console.CursorTop)

    writeInput()
    let mutable key = Console.ReadKey(true)
    
    while key.Key <> ConsoleKey.Enter do
        match key.Key with
        | ConsoleKey.LeftArrow ->
            if cursorIndex > 0 then
                cursorIndex <- cursorIndex - 1
                Console.SetCursorPosition(cursorIndex + promptLen, Console.CursorTop)
        | ConsoleKey.RightArrow ->
            if cursorIndex < currentInput.Length then
                cursorIndex <- cursorIndex + 1
                Console.SetCursorPosition(cursorIndex + promptLen, Console.CursorTop)
        | ConsoleKey.UpArrow ->
            if currentPos > 0 then
                currentPos <- currentPos - 1
                currentInput <- previousMsgs.[currentPos]
                cursorIndex <- currentInput.Length
                writeInput()
        | ConsoleKey.DownArrow ->
            if currentPos < previousMsgs.Count - 1 then
                currentPos <- currentPos + 1
                currentInput <- previousMsgs.[currentPos]
                cursorIndex <- currentInput.Length
                writeInput()
        | ConsoleKey.Backspace ->
            if cursorIndex > 0 then
                currentInput <- currentInput.Remove(cursorIndex - 1, 1)
                cursorIndex <- cursorIndex - 1
                writeInput()
        | ConsoleKey.Home ->
            cursorIndex <- 0
            Console.SetCursorPosition(promptLen, Console.CursorTop)
        | ConsoleKey.End ->
            cursorIndex <- currentInput.Length
            Console.SetCursorPosition(cursorIndex + promptLen, Console.CursorTop)      
        | _ ->
            if not (Char.IsControl(key.KeyChar)) then
                currentInput <- currentInput.Insert(cursorIndex, key.KeyChar.ToString())
                cursorIndex <- cursorIndex + 1
                writeInput()
        
        key <- Console.ReadKey(true)
    
    Console.WriteLine()
    currentInput

seenCustomUnits.Clear()

let rec generalRepl prefilloutput parseFunc evalFunc prettyPrintFunc counter prevOutput =
    printf $"In [{counter}]: "
    let input = getInputWithHistory prefilloutput (previousMsgs.Count - 1) prevOutput
    previousMsgs.Add(input)
    
    if input.ToLower() <> "q" then 
        match parseFunc input with
        | Result.Ok parsedExpr ->  
            let result = evalFunc parsedExpr
            let output = prettyPrintFunc input result
            printfn $"Out[{counter}]: {output}" 
            generalRepl prefilloutput parseFunc evalFunc prettyPrintFunc (counter + 1) (convertSuperscripts output)
        | Result.Error msg -> 
            printfn "Error: %s" msg
            generalRepl prefilloutput parseFunc evalFunc prettyPrintFunc counter prevOutput
    else 
        printfn "Exiting REPL."

let repl = 
    generalRepl 
        true 
        parse 
        eval 
        (fun s exprchoice -> 
            ExpressionChoice.PrettyPrint(exprchoice))

let dicerepl = 
    generalRepl 
        false
        DiceRollerMathParser.runParser 
        (_.Eval()) 
        (fun _ -> function Result.Ok dice -> DiceRollerMathParser.DiceExpr.InfoString dice | Result.Error s -> s)

[<EntryPoint>]
let main argv =
    printfn "Welcome to the mathlang REPL. Type 'q' to quit."

    let replChoice =
        if argv.Length > 0 then argv.[0]
        else
            printfn "Choose REPL mode: 0 for calc, 1 for dice"
            Console.ReadLine()

    match replChoice with
    | "0" | "--calc" | "-c" -> printfn "Calculator mode selected."; repl 1 ""
    | "1" | "--dice" | "-d" -> printfn "Dice calculator mode selected."; dicerepl 1 ""
    | _ -> printfn "Invalid choice. Exiting."
    
    0