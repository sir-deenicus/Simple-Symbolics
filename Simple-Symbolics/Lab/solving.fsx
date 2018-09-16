#load "Core.fsx"

open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics
open MathNet.Symbolics

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

let symbols = (Map["r", FloatingPoint.Real 1.; 
                   "v", FloatingPoint.Real 2.355
                   "a", FloatingPoint.Complex (complex 2. 3.);
                   "b", FloatingPoint.Real 2.])

let eq3 = a * b + 3/(2 * Expression.Ln x ** 3) 

containsVar x (eq3)

let eq2 = 3Q/4Q * π * r ** 3

let pn = 1/2Q * a * t**2 

Evaluate.evaluate symbols eq2

Infix.format eq2

let eqt,eqt2 = rinverseAndPartitionVar t pn

eqt2.Value |> snd |> Infix.format
eqt.Value |> Infix.format
/////////////////////

let p1 = x ** 3 - 4 * x ** 2 - 7 * x + 10

let p1' = x ** 3 - 4 * x ** 2 - 7 * x  

let p2 = x ** 3 + 6 * x ** 2 + 5 * x - 12

let p3 = x ** 5 - 4*x**4 - 7 * x**3 + 14 * x **2 - 44 * x + 120
 
let quadraticSolve p = 
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
       let coeffs = Polynomial.coefficients x p
       let a,b,c = coeffs.[2], coeffs.[1], coeffs.[0]
       (-b + sqrt(b**2 - 4 * a * c)) / (2 * a), (-b - sqrt(b **2 - 4 * a * c)) / (2 * a)
    else failwith "Not quadratic"
 
factors id id 6

let ac,bc = quadraticSolve (x**2 + 53 * x + 12)

pairmap (Rational.reduce >> Infix.format) (ac,bc) 

quadraticSolve (a * x**2 + b) |> pairmap Infix.format

open System.Collections.Generic

let rec tryFactorizePolynomial x fx =
    let constant = Polynomial.coefficient x 0 fx 
    let deg = Polynomial.degree x fx
    if constant = 0Q && deg.ToInt() < 2 then [], []
    elif deg.ToInt() = 1 then [-constant], []
    elif constant = 0Q then 
      let fx', _  = Polynomial.divide x fx x
      let sols, eq = tryFactorizePolynomial x fx'  
      0Q::sols, fx'::eq
    else
      let factors = factorsExpr (abs constant)
      let r,s =
         List.unzip
           [for f in (List.map ((*) -1) factors) @ factors do
                  let n = f.ToFloat()  
                  let value = Evaluate.evaluate (Map ["x", FloatingPoint.Real n]) fx
                  if value.RealValue = 0. then 
                      yield (f, Polynomial.divide x fx (x - f) |> fst) ] 
      let sols, eq = List.map (tryFactorizePolynomial x) s |> List.unzip
      r @ List.concat sols |> HashSet |> Seq.toList, s @ List.concat eq |> HashSet |> Seq.toList
   
let res = tryFactorizePolynomial x p3

res |> pairmap (List.map Infix.format)
res |> snd |> List.filter (Polynomial.degree x >> ((=) 2Q)) |> List.map (quadraticSolve >> pairmap (Algebraic.simplify true >> Rational.simplify x >> Infix.format))



