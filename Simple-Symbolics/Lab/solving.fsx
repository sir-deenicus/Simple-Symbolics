#load "Core.fsx"

open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics

type ExprType = IsSum | IsProduct | IsOther | Zero

let inverse f (e:Expression) =  
    match (e,f) with 
    | x ,IsSum -> -x
    | x, IsProduct -> 1 / x 
    
let rec rinverseAndPartitionVar s = function 
    | Sum l as pl -> 
        let matches,fails = List.partition (containsVar s) l
        printfn "m,f: %A" (matches,fails)
        let fl = List.map (inverse IsSum) fails
        printfn "fl: %A" fl
                     
        let m, mf = rinverseAndPartitionVar s matches.Head
        printfn "%A" m
        printfn "mf: %A" mf
                     
        match mf with 
            None -> m, Some (IsSum, Sum fl) 
          | Some (t,x) -> 
            printfn "x: %A" x
            printfn "+++++++++"
            let op = match t with IsSum -> (+) | IsProduct -> (*) |  _ -> (+) 
            m, Some(IsSum, op x (Sum fl))
              
    | Product l as pl -> 
      
      let matches,fails = List.partition (containsVar s) l
      printfn "m,f: %A" (matches,fails)
      let fl = List.map (inverse IsProduct) fails
      printfn "%A" fl
                         
      let m, mf = rinverseAndPartitionVar s matches.Head
      printfn "%A" m
      printfn "%A" mf
      printfn "**" 
                         
      match mf with 
          None -> m, Some (IsProduct,Product fl) 
        | Some (t,x) -> 
          let op = match t with IsSum -> (+) | IsProduct -> (*) |  _ -> (+) 
          m, Some(IsProduct, op x (Product fl))
    | x -> if containsVar s x then Some x, None else None,Some (Zero, x)

let simp = (a+b) + x / (r+y)
let eqx,eqy = rinverseAndPartitionVar y (simp)

eqy.Value |> snd |> Infix.format
eqx.Value |> Infix.format



containsVar y simp 

let symbols = (Map["π", FloatingPoint.Real 3.14;
                   "r", FloatingPoint.Real 1.; 
                   "v", FloatingPoint.Real 2.355])

let symbols2 = (Map["a", FloatingPoint.Complex (complex 2. 3.);
                    "b", FloatingPoint.Real 2.])

let eq3 = a * b + 3/(2 * Expression.Ln x ** 3) 

containsVar x (eq3)


let eq2 = 3Q/4Q * π * r ** 3

Evaluate.evaluate symbols eq2

Infix.format eq2