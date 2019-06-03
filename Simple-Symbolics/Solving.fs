module MathNet.Symbolics.Solving
 
open MathNet.Symbolics
open Core
open Vars 

let reArrangeExprEquationX silent focusVar (left,right) = 
    let rec iter fx ops = 
        match fx with    
        | f when f = focusVar -> f, ops
        | Power(f, p) -> 
            if not silent then printfn "raise to power"; 
            iter f ((fun (x:Expression) -> x**(1/p))::ops) 
        | Sum []     | Sum [_]
        | Product [] | Product [_] -> fx, ops
        | Product l -> 
           if not silent then printfn "divide";  
           let matched, novar = List.partition (containsVar focusVar) l 
           let ops' = match novar with [] -> ops | _ -> (fun x -> x/(Product novar))::ops
           match matched with
           | [] -> fx, ops'
           | [h] -> iter h ops'
           | hs -> Product hs, ops'
        | Sum l -> 
            if not silent then printfn "subtract"; 
            let matched, novar = List.partition (containsVar focusVar) l
            let ops' = match novar with [] -> ops | _ -> (fun x -> x - (Sum novar))::ops
            match matched with
             | [] -> fx, ops'
             | [h] -> iter h ops'
             | hs -> Sum hs, ops'
        | Function(Ln, x) -> 
          if not silent then printfn "exponentiate"; 
          iter x (exp::ops)
        | Function(Tan, x) -> 
          if not silent then printfn "atan"; 
          iter x ((fun x -> Function(Atan, x))::ops)  
        | Function(Cos, x) -> 
          if not silent then printfn "acos"; 
          iter x ((fun x -> Function(Acos, x))::ops)
        | Function(Exp, x) -> 
          if not silent then printfn "log"; 
          iter x (ln::ops)
        | _ -> failwith "err"
    let f, ops = iter left [] 
    f, ops |> List.rev |> List.fold (fun e f -> f e) right |> Algebraic.simplify true      

let reArrangeExprEquation focusVar (left,right) = reArrangeExprEquationX false focusVar (left,right)

let rec invertFunction x expression = 
    printfn "%s" (expression |> Infix.format)
    match reArrangeExprEquation x (expression, x) with
     | Identifier (Symbol _) as y, inv when y = x -> inv
     | _, inv -> printfn "Did not completely reduce. Collecting terms";
                 printfn "Is it monomial in x?"
                 let monom = Polynomial.collectTerms x expression
                 if Polynomial.isMonomial x monom then
                    printfn "Yes"  
                    invertFunction x monom
                 else printfn "no";inv

let quadraticSolve p = 
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
       let coeffs = Polynomial.coefficients x p
       let a,b,c = coeffs.[2], coeffs.[1], coeffs.[0]
       Algebraic.simplify true ((-b + sqrt(b**2 - 4 * a * c)) / (2 * a)), 
       Algebraic.simplify true ((-b - sqrt(b **2 - 4 * a * c)) / (2 * a)) 
    else failwith "Not quadratic"

let completeSquare x  p = 
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
       let coeffs = Polynomial.coefficients x p
       let a,b,c = coeffs.[2], coeffs.[1], coeffs.[0]
       a * (x + b/(2*a)) ** 2 + c - b**2/(4*a) 
    else failwith "Not quadratic"


let reArrangeEquation focusVar (e:Equation) = 
    reArrangeExprEquation focusVar e.Definition 
    |> Equation


