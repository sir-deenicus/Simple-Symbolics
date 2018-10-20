#load "Core.fsx"
open System.Collections.Generic

open MathNet.Symbolics
open Core
open Vars
open MathNet.Numerics
open MathNet.Symbolics

type ExprType = IsSum | IsProduct | NonOp

let unSumOrMult f (e:Expression) =  
    match (e,f) with 
    | x ,IsSum -> -x
    | x, IsProduct -> 1 / x 
    | _ -> failwith "error" 
let rec matchGroupAndInverse sumOrProduct isSumOrProduct s l =     
    let matches,fails = List.partition (containsVar s) l
    printfn "matches: %A\nfails: %A" matches fails
    let inverteds = List.map (unSumOrMult isSumOrProduct) fails
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


let reArrangeEquation s (l,r) = 
    let rec iter fx ops = 
        match fx with    
        | f when f = s -> f, ops
        | Power(f, p) -> 
            printfn "raise to power"; 
            iter f ((fun (x:Expression) -> x**(1/p))::ops) 
        | Sum []     | Sum [_]
        | Product [] | Product [_] -> fx, ops
        | Product l -> 
           printfn "divide";  
           let matched, novar = List.partition (containsVar s) l 
           let ops' = match novar with [] -> ops | _ -> (fun x -> x/(Product novar))::ops
           match matched with
           | [] -> fx, ops'
           | [h] -> iter h ops'
           | hs -> Product hs, ops'
        | Sum l -> 
            printfn "subtract"; 
            let matched, novar = List.partition (containsVar s) l
            let ops' = match novar with [] -> ops | _ -> (fun x -> x - (Sum novar))::ops
            match matched with
             | [] -> fx, ops'
             | [h] -> iter h ops'
             | hs -> Sum hs, ops'
        | Function(Ln, x) -> printfn "exponentiate"; iter x (exp::ops)
        | Function(Cos, x) -> printfn "acos"; iter x ((fun x -> Function(Acos, x))::ops)
        | Function(Exp, x) -> printfn "log"; iter x (log::ops)
        | _ -> failwith "err"
    let f, ops = iter l [] 
    f, ops |> List.rev |> List.fold (fun e f -> f e) r  

reArrangeEquation x (x**2 + x,0Q) |> (fun (x,y) -> x , y)

let symbols = (Map["r", FloatingPoint.Real 1.; 
                   "v", FloatingPoint.Real 2.355
                   "a", FloatingPoint.Complex (complex 2. 3.);
                   "b", FloatingPoint.Real 2.])

///////////////
type Hashset<'a> = System.Collections.Generic.HashSet<'a> 
let expressionToList = function 
     | Sum l
     | Product l -> l
     | x -> [x]
let letTryReplace r (xhs: Hashset<_>) (l:_ list) =
        let hs = Hashset l
        if xhs.IsSubsetOf hs then 
           hs.SymmetricExceptWith xhs 
           r::List.ofSeq hs
        else l
let replaceSymbolFull r x formula = 
   let xhs = Hashset(expressionToList r)    
   let rec iter = function
   | Identifier _ as sy when sy = x -> r
   | Power(Identifier (Symbol _) as sy, n) when sy = x -> Power(r, n)   
   | Power(Function(f, (Identifier (Symbol _) as sy)), n) when sy = x -> Power(Function(f, r), n)
   |       Function(f, (Identifier (Symbol _ ) as sy))    when sy = x -> Function(f, r)
   | Power(Sum l, n)      -> Power(Sum     (List.map iter (letTryReplace r xhs l)), n)
   | Power(Product l, n)  -> Power(Product (List.map iter (letTryReplace r xhs l)), n)
   | Power(Function(f, Sum l), n) -> Power(Function(f, Sum (List.map iter (letTryReplace r xhs l))),n)
   | Power(Function(f, Product l), n) -> Power(Function(f, Product (List.map iter (letTryReplace r xhs l))),n)
   |       Function(f, Product l)  ->          Function(f, Product (List.map iter (letTryReplace r xhs l)))
   |       Function(f, Sum l)  ->              Function(f, Sum (List.map iter (letTryReplace r xhs l))) 
   | Product l ->  Product (List.map iter (letTryReplace r xhs l))
   | Sum     l ->  Sum     (List.map iter (letTryReplace r xhs l))
   | x -> x
   iter formula |> Algebraic.simplify true

log 1. - log 2. - log 3.
log (1./2./3.)
module Logarithms =
  let expand = function 
   | Function(Ln, Product l) -> Sum(List.map (function Power(x, n) when n = -1Q -> ln (-x) | x -> ln x) l)
   | f -> f
  let contract = function 
    | Sum l -> 
       let logs, rest = 
           List.partition (function 
             | Function(Ln,_) -> true 
             | Product[n;Function(Ln, _)] when n = -1Q -> true
             | _ -> false) l
       let logs' = 
           logs |> List.map (function 
                     | Product[n;Function(Ln, x)] when n = -1Q -> 1/x 
                     | Function(Ln, x) -> x 
                     | _-> failwith "never")
       ln(Product logs') + Sum rest
    | f -> f

Logarithms.contract (ln a - ln b)

log 2. - log 3. + log 4.

ln (a/b)

log ((2. * 4.) / 3.)
let sigma2,sigma1 = Operators.symbol "\sigma_2",Operators.symbol "\sigma_1"

let zz = (1/2Q * ln(2 * pi * sigma2 ** 2) + -1/2Q * (1 + ln(2 * pi * sigma1 ** 2)) )
Logarithms.contract (1/2Q * ln(2 * pi * sigma2 ** 2) + -1/2Q * (1 + ln(2 * pi * sigma1 ** 2)) )

Structure.collect (function Function (Ln, x) -> Some x | _ -> None) zz

zz |>  Algebraic.expand


(2 * pi * sigma2 ** 2)
(1/2Q * ln(2 * pi * sigma2 ** 2) + -1/2Q * (1 + ln(2 * pi * sigma1 ** 2)) ) |> replaceSymbolFull (2 * pi * sigma2 ** 2) x
(1/2Q * ln(2 * pi * sigma2 ** 2) + -1/2Q * (1 + ln(2 * pi * sigma1 ** 2)) ) |> containsVar sigma2

replaceSymbolFull x (b * c) (b * c * 2 * sqrt(3 * b * c + 4))
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
replaceSymbolFull (2Q/3Q) x p5 |> Rational.simplify x |> Infix.format
p5.ToFormattedString()
 