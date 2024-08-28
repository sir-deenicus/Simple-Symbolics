open System
open Parser
open System.Collections.Generic

let previousMsgs = ResizeArray()

let convertSuperscripts (input: string) =
    let superscripts = "⁰¹²³⁴⁵⁶⁷⁸⁹"
    input.ToCharArray()
    |> Array.map (fun c ->
        match superscripts.IndexOf(c) with
        | -1 -> c.ToString()
        | n -> "^" + n.ToString())
    |> String.concat ""

let rec getInputWithHistory pos (prevMsg:string) =
    let mutable currentPos = pos
    let mutable currentInput = prevMsg
    let mutable cursorIndex = currentInput.Length
    let promptLen = $"In [{pos+2}]: ".Length
    
    let writeInput() =
        Console.SetCursorPosition(0, Console.CursorTop)
        Console.Write(new string(' ', Console.WindowWidth - 1))
        Console.SetCursorPosition(0, Console.CursorTop)
        Console.Write($"In [{pos+2}]: " + currentInput)
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

let seenCustomUnits = HashSet<string>()

let rec repl counter prevOutput =
    printf $"In [{counter}]: "
    let input = getInputWithHistory (previousMsgs.Count - 1) prevOutput
    previousMsgs.Add(input)
    
    if input.ToLower() <> "q" then 
        match parse input with
        | Result.Ok ast -> 
            let result = eval seenCustomUnits ast
            let output = ExpressionChoice.PrettyPrint(seenCustomUnits, "", result)
            printfn $"Out[{counter}]: {output}" 
            repl (counter + 1) (convertSuperscripts output)
        | Result.Error msg -> 
            printfn "Error: %s" msg
            repl counter prevOutput
    else 
        printfn "Exiting REPL."

[<EntryPoint>]
let main argv =
    printfn "Welcome to the mathlang REPL. Type 'q' to quit."
    repl 1 ""
    0