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

let pn = 1/2Q * a * t**2 


Evaluate.evaluate symbols eq2

Infix.format eq2

let eqt,eqt2 = rinverseAndPartitionVar t pn

eqt2.Value |> snd |> Infix.format
eqt.Value |> Infix.format
/////////////////////


let p1 = x ** 3 - 4 * x ** 2 - 7 * x + 10

let p1' = x ** 3 - 4 * x ** 2 - 7 * x  

let p2 = x ** 5 - 4*x**4 - 7 * x**3 + 14 * x **2 - 44 * x + 120

let inline factors toint f x = let x' = toint x in [|for n in 1..x' / 2 do if x' % n = 0 then yield f n |]
let toInt = function (Number n) -> n | _ -> failwith "not a number"
factors (toInt >> int) Expression.FromInt32 100Q


let pairmap f (x,y) = f x , f y
 
let quadratic p = 
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
       let coeffs = Polynomial.coefficients x p
       let a,b,c = coeffs.[2], coeffs.[1], coeffs.[0]
       (-b + sqrt(b**2 - 4 * a * c)) / (2 * a), (-b - sqrt(b **2 - 4 * a * c)) / (2 * a)
    else failwith "Not quadratic"

let quadratic2 a b c =  
    let descr:Expression = b**2Q - 4Q * a * c
    let a2 = 2Q * a
    if descr.ToFloat() < 0. then Complex(-b/a2, sqrt -descr / a2), Complex(-b/a2, -sqrt -descr / a2) 
    else Complex((-b + sqrt descr) / (2Q * a)), Complex ((-b - sqrt descr) / (2Q * a))
           
let quadratic3 a b c =  
    let descr:Expression = b**2Q - (4Q * a * c)
    printfn "%A" (b, b**2Q, a,c, 4Q*a*c)
    let a2 = 2Q * a
    (-b + sqrt descr) /a2, (-b - sqrt descr) / a2
 
let cubic2 a b c d =
    let A = 1Q/a * (c - b**2Q / (3Q * a))
    let B = 1Q/a * (d + 2Q * b**3Q/(27Q * a ** 2Q) - b * c /(3Q * a) )
    let s = A/3Q

    let fsolve (x:Complex) =  
        let a1 = x ** (1Q/3Q)
        let a2 = x.Pow(1Q/3, 2 * pi)
        let a3 = x.Pow(1Q/3, 4 * pi)
        (a1 - 3Q/a1) + Complex 3Q, (a2 - 3Q/a2) + Complex 3Q, (a3 - 3Q/ a3) + Complex 3Q
    
    let triplemap f (a,b,c) = f a, f b, f c 
    //let fm = triplemap (fun (c:Complex) -> c.ToComplex())
    let (sa,sb) = quadratic3 1Q -B (-(s**3Q))
    let sv = (-B + sa) ** (1Q/3Q)
    let tv = sa ** (1Q/3)

    //fm (fsolve sa),fm (fsolve sb), (A ** 3 / 27Q)
    [A; B;s; sv;tv;sv - tv] |> List.map (fun f -> f.ToFloat())// Infix.format f )
 
let zz = cubic2 2Q -30Q 162Q -350Q
let zz2 = cubic2 1Q -4Q -7Q 10Q
12. * sqrt 3.
sqrt(432.)
System.Math.Pow((10. + 6. * sqrt 3.),1./3.)

(20. + (-20. + sqrt(432.))/2.) ** (1./3.)
quadratic2 1Q 3Q 3Q //|> pairmap (fun c -> c.ToComplex())
sqrt 3./ 2.
(quadratic (x **2 + 3*x + 3) |> fst).ToComplex()
cubic2 a b c d 

let cubic a b c d =
     let ξ = Complex(-1/2Q, 1/2 * sqrt 3Q)
     let Δ = 18Q * a * b * c * d - 4 * b ** 3 * d + b ** 2 * c ** 2 - 4 * a * c ** 3 - 27 * a ** 2 * d ** 2
     let Δ_0 = b ** 2 - 3 * a * c
     if Δ = 0Q && Δ_0 = 0Q then [Complex (-b/(3 * a))]
     else
     let Δ_1 = 2 * b ** 3 - 9 * a * b * c + 27 * a ** 2 * d 
     let C = ((Δ_1 + sqrt(Δ_1 ** 2 - 4 * Δ_0 ** 3)) / 2) ** (1/3)

     [for k in 0..2 -> 
       let ξkC = ξ ** k * C
       (-1/ (3 * a)) * (Complex b + ξkC + Δ_0 / ξkC )]

let cl = cubic 10Q -7Q -4Q 1Q
cl |> List.map (fun c -> c.ToComplex())

MathNet.Numerics.FindRoots.Cubic (10., -7., -4., 1.)

BigRational.fromFloat  2.96059473233375E-16


let ac,bc = quadratic (x**2 + 53 * x + 12)

pairmap (Rational.reduce >> Infix.format) (ac,bc) 

quadratic (x**2 + 1) |> pairmap Infix.format
