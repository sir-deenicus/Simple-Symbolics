open System 
open Parser 

let rec repl counter =
    printf $"In [{counter}]: "
    let input = Console.ReadLine()
    if input.ToLower() <> "q" then 
        match parse input with
        | Result.Ok ast -> 
            let result = eval ast
            printfn $"Out[{counter}]: {ExpressionChoice.PrettyPrint result}" 
        | Result.Error msg -> printfn "Error: %s" msg
        repl (counter + 1)
    else printfn "Exiting REPL."

[<EntryPoint>]
let main argv =
    printfn "Welcome to the mathlang REPL. Type 'q' to quit."
    repl 1
    0
