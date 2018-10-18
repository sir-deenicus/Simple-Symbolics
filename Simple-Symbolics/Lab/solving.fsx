#load "Core.fsx"

open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics
open MathNet.Symbolics

type ExprType = IsSum | IsProduct | NonOp

let inverse f (e:Expression) =  
    match (e,f) with 
    | x ,IsSum -> -x
    | x, IsProduct -> 1 / x 
    | _ -> failwith "error"

let rec matchGroupAndInverse sumOrProduct isSumOrProduct s l =     
    let matches,fails = List.partition (containsVar s) l
    printfn "matches: %A\nfails: %A" matches fails
    let inverteds = List.map (inverse isSumOrProduct) fails
    printfn "Inverteds: %A" inverteds
                 
    let m, matchfails = rinverseAndPartitionVar s matches.Head
    printfn "Recursive Matched: %A" m
    printfn "Recursive Failed: %A" matchfails
                 
    match matchfails with 
        None -> m, Some (isSumOrProduct, sumOrProduct inverteds) 
      | Some (t,x) -> 
        printfn "x: %A" x
        printfn "+++++++++"
        let op = match t with IsSum -> (+) | IsProduct -> (*) |  _ -> (+) 
        m, Some(isSumOrProduct, op x (sumOrProduct inverteds))

and rinverseAndPartitionVar s = function 
    | Sum l -> matchGroupAndInverse Sum IsSum s l 
    | Product l -> matchGroupAndInverse Product IsProduct s l
    | f -> if containsVar s f then Some f, None else None,Some (NonOp, f)

let reduce s (l,r) = 
    let rec iter fx ops = 
        match fx with    
        | f when f = s -> ops
        | Power(f, Number n) when n > 0N -> printfn "raise to power"; iter f ((fun (x:Expression) -> x **(-1/Number n))::ops)
        | Power(f, Number n) when n < 0N -> printfn "raise to power"; iter f ((fun (x:Expression) -> x ** (1/Number n))::ops)
        | Sum []
        | Product []
        | Sum [_]
        | Product [_] -> ops
        | Product l -> printfn "divide"; 
                       let matched, novar = List.partition (containsVar s) l 
                       iter (Product matched) ((*) ((1/(Product novar)))::ops)
        | Sum l -> 
            printfn "subtract"; 
            let matched, novar = List.partition (containsVar s) l 
            iter (Sum matched) ((+) ((-(Product novar)))::ops)
        | Function(Ln, x) -> printfn "exponentiate"; iter x (exp::ops)
        | Function(Exp, x)  -> printfn "log"; iter x (log::ops)
        | _ -> failwith "err"
    iter l [] |> List.rev |> List.fold (fun e f -> f e) r

let fullinverse s (l,r) = 
    let rec iter fx ops = 
        match fx with    
        | f when f = s -> ops
        | Power(f, Number n) when n > 0N -> 
            printfn "raise to power"; 
            iter f ((fun (x:Expression) -> x **(-1/Number n))::ops)
        | Power(f, Number n) when n < 0N -> printfn "raise to power"; iter f ((fun (x:Expression) -> x ** (1/Number n))::ops)
        | Sum []
        | Product []
        | Sum [_]
        | Product [_] -> ops
        | Product l -> printfn "divide";  
                       let matched, novar = List.partition (containsVar s) l 
                       let ops' = ((*) ((1/(Product novar))))::ops
                       match matched with
                       | [] -> ops'
                       | [h] | h::_ -> iter h ops'
        | Sum l -> 
            printfn "subtract"; 
            let matched, novar = List.partition (containsVar s) l
            let ops' = ((+) (-(Sum novar)))::ops
            match matched with
             | [] -> ops'
             | [h] |  h::_ -> iter h ops' 
        | Function(Ln, x) -> printfn "exponentiate"; iter x (exp::ops)
        | Function(Exp, x)  -> printfn "log"; iter x (log::ops)
        | _ -> failwith "err"
    s,iter l [] |> List.rev |> List.fold (fun e f -> f e) r   
let simp = (a+b) + x / (r+y)
let eqx,eqy = rinverseAndPartitionVar y (simp)

eqy.Value |> snd |> Infix.format
eqx.Value |> Infix.format

reduce y (eqx.Value, eqy.Value |> snd) 

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

let eqt,eqt2 = rinverseAndPartitionVar a eq3

eqt2.Value |> snd |> Infix.format
eqt.Value |> Infix.format
/////////////////////

let p1 = x ** 3 - 4 * x ** 2 - 7 * x + 10

let p1' = x ** 3 - 4 * x ** 2 - 7 * x  

let p2 = x ** 3 + 6 * x ** 2 + 5 * x - 12

let p3 = x ** 5 - 4*x**4 - 7 * x**3 + 14 * x **2 - 44 * x + 120

let p4 = x ** 3 + x - 1
 
let p5 = 3 * x ** 3 - 5 * x ** 2 + 5 * x - 2

let quadraticSolve p = 
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
       let coeffs = Polynomial.coefficients x p
       let a,b,c = coeffs.[2], coeffs.[1], coeffs.[0]
       (-b + sqrt(b**2 - 4 * a * c)) / (2 * a), (-b - sqrt(b **2 - 4 * a * c)) / (2 * a)
    else failwith "Not quadratic"
 
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
  
 
let res = tryFactorizePolynomial x p5
let mm = Polynomial.divide x p5 3Q |> fst 
//|> pairmap Infix.format
res |> pairmap (List.map Infix.format)
res |> snd |> List.filter (Polynomial.degree x >> ((=) 2Q)) |> List.map (quadraticSolve >> pairmap (Algebraic.simplify true >> Rational.simplify x >> Infix.format))

Structure.substitute 1Q x p5  

Structure.map (function | Identifier (Symbol "x") -> printfn "eg"; 1Q | x -> x) p5
replaceSymbol (2Q/3Q) x p5 |> Rational.simplify x |> Infix.format
p5.ToFormattedString()
 