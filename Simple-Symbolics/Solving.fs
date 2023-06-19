module MathNet.Symbolics.Solving

open MathNet.Symbolics
open Core
open Vars
open Prelude.Common 
open Utils
open MathNet.Symbolics.NumberProperties
open Units
open Equations
open MathNet.Symbolics.Operators

let quadraticSolve x p =
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
        let coeffs = Polynomial.coefficients x p
        let a, b, c = coeffs.[2], coeffs.[1], coeffs.[0]
        Expression.simplify ((-b + sqrt (b ** 2 - 4 * a * c)) / (2 * a)),
        Expression.simplify ((-b - sqrt (b ** 2 - 4 * a * c)) / (2 * a))
    else failwith "Not quadratic"

let completeSquare x p =
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
        let coeffs = Polynomial.coefficients x p
        let a, b, c = coeffs.[2], coeffs.[1], coeffs.[0]
        a * (x + b / (2 * a)) ** 2 + c - b ** 2 / (4 * a)
    else failwith "Not quadratic"

module Polynomial =
    //Sometimes there might be rational coefficients. So multiply by denominators to get out integers.
    ///Returns Least Common multiple of denominator coefficients and polynomial with integer coefficients from multiplying by lcm
    let toIntegerCoefficients fx =
        let denominators =
            [ for c in Polynomial.coefficients x fx do
                   if not (Expression.isInteger c) then yield Rational.denominator c ]
           
        if List.isEmpty denominators then 1Q, fx 
        else  
            // get rid of denominators by multiplying by their least common multiple  
            let lcm = Numbers.lcm denominators
            if lcm = undefined then 1Q, fx
            else lcm, fx * lcm |> Algebraic.expand 
 
    ///The rational roots method to factor polynomials with rational roots with degree > 2
    let factor x fx =
        //this will iterate 
        let rec loop zeros fx =

            //Simple cases
            let deg = Polynomial.degree x fx
        
            if deg = 0Q then (fx, Operators.undefined)::zeros
            elif deg = 1Q then
                let coeff = Polynomial.coefficient x 1 fx 
                let constant = Polynomial.coefficient x 0 fx
                (fx, (-constant / coeff))::zeros
            elif deg = 2Q then
                let a,b = quadraticSolve x fx 
                (x-a,a)::(x-b,b)::zeros
            else //Get all the Polynomial coefficients and their factors.      
                let coeffs = Polynomial.coefficients x (toIntegerCoefficients fx |> snd) 
                if Array.forall Expression.isInteger coeffs then //Ensure integer coefficients
                    let numfactors = Array.collect (abs >> factorsExpr >> List.toArray) coeffs |> Hashset

                    //evaluate each candidate and its negation, collecting all inputs
                    //which evaluate to zero.
                    let pfactors =
                        [ for f in numfactors do
                            yield!
                                [for fval in [f;-f] do
                                    let eval = replaceSymbolWith fval x fx |> Expression.fullSimplify
                                    if eval = 0Q then yield x - fval, fval ]]
                    match pfactors with 
                    | [] -> zeros
                    | _ -> 
                        //The factors can be multiplied such that dividing by them leaves 
                        //us with a simpler polynomial. 
                        let p = pfactors |> List.map fst |> List.reduce (*) |> Algebraic.expand
                        let fx', rem = Polynomial.divide x fx p
                        if rem <> 0Q then failwith "Polynomial factoring unexpected error"
                        loop (pfactors @ zeros) fx'
                else zeros 
        
        let fs, zs = List.unzip(loop [] fx)

        (match fs with
         | [] -> None
         | _ -> Some(Product fs)), List.filter ((<>) Operators.undefined) zs

let internal reArrangeExprInequality silent focusVar (left, right) =
    let rec iter doflip fx ops =
        match fx with
        | f when f = focusVar -> doflip, f, ops
        | Power(b, x) when containsVar focusVar x -> 
            iter doflip x ((fun x -> log b x)::ops)
        | Sum [] | Sum [ _ ] | Product [] | Product [ _ ] -> doflip, fx, ops
        | Product l ->
            if not silent then printfn "divide"
            let matched, novar = List.partition (containsVar focusVar) l 
            match novar with 
            | [v] when Expression.isNumber v || Expression.isPositive v -> 
                let doflip = Expression.isNegativeNumber v
                let ops' =
                    match novar with
                    | [] -> ops
                    | _ -> (fun x -> x / (Product novar)) :: ops
                match matched with
                | [] -> doflip,fx, ops'
                | [ h ] -> iter doflip h ops'
                | hs -> doflip,Product hs, ops'
            | _ -> doflip,Undefined, ops
        | Sum l ->
            if not silent then printfn "subtract"
            let matched, novar = List.partition (containsVar focusVar) l

            let ops' =
                match novar with
                | [] -> ops
                | _ -> (fun x -> x - (Sum novar)) :: ops
            match matched with
            | [] -> doflip,fx, ops'
            | [ h ] -> iter doflip h ops'
            | hs -> doflip,Sum hs, ops'
        | FunctionN(Log, [b;x]) ->
            if not silent then printfn "exponentiate"
            iter doflip x ((fun x -> b ** x) :: ops)
        | Function(Ln, x) ->
            if not silent then printfn "exponentiate"
            iter doflip x (exp :: ops) 
        | Function(Exp, x) ->
            if not silent then printfn "log"
            iter doflip x (ln :: ops)
        | _ -> doflip,Undefined, ops //failwith "err"

    let doflip, f, ops = iter false left []
    doflip,
    f,
    ops
    |> List.rev
    |> List.fold (fun e f -> f e) right
    |> Expression.simplify 

let internal reArrangeExprEquation silent focusVar (left, right) =
    let rec iter fx ops =
        match fx with
        | f when f = focusVar -> f, ops
        | Power(b, x) when containsVar focusVar x -> 
            iter x ((fun x -> log b x)::ops)
        | Power(f, p) ->
            if not silent then printfn "raise to power"
            iter f ((fun (x : Expression) -> x ** (1 / p)) :: ops)
        | Sum [] | Sum [ _ ] | Product [] | Product [ _ ] -> fx, ops
        | Product l ->
            if not silent then printfn "divide"
            let matched, novar = List.partition (containsVar focusVar) l

            let ops' =
                match novar with
                | [] -> ops
                | _ -> (fun x -> x / (Product novar)) :: ops
            match matched with
            | [] -> fx, ops'
            | [ h ] -> iter h ops'
            | hs -> Product hs, ops'
        | Sum l ->
            if not silent then printfn "subtract"
            let matched, novar = List.partition (containsVar focusVar) l

            let ops' =
                match novar with
                | [] -> ops
                | _ -> (fun x -> x - (Sum novar)) :: ops
            match matched with
            | [] -> fx, ops'
            | [ h ] -> iter h ops'
            | hs -> Sum hs, ops'
        | FunctionN(Log, [b;x]) ->
            if not silent then printfn "exponentiate"
            iter x ((fun x -> b ** x) :: ops)
        | Function(Ln, x) ->
            if not silent then printfn "exponentiate"
            iter x (exp :: ops)
        | Function(Tan, x) ->
            if not silent then printfn "atan"
            iter x ((fun x -> Function(Atan, x)) :: ops)
        | Function(Erf, x) ->
            if not silent then printfn "erf^-1"
            iter x ((fun x -> Function(ErfInv, x)) :: ops)
        | Function(Cos, x) ->
            if not silent then printfn "acos"
            iter x ((fun x -> Function(Acos, x)) :: ops)
        | Function(Sin, x) ->
            if not silent then printfn "asin"
            iter x ((fun x -> Function(Asin, x)) :: ops) 
        | IsDerivative(_, f, dx) ->
            if not silent then printfn "integrate"
            iter f ((fun x -> integral dx x) :: ops) 
        | IsIntegral(f, dx) ->
            if not silent then printfn "differentiate"
            iter f ((fun x -> diff dx x) :: ops) 
        | Function(Exp, x) ->
            if not silent then printfn "log"
            iter x (ln :: ops)
        | _ -> Undefined, ops //failwith "err"

    let f, ops = iter left []
    f,
    ops
    |> List.rev
    |> List.fold (fun e f -> f e) right
    |> Expression.simplify 
      
let reArrangeEquation focusVar (e : Equation) =
    reArrangeExprEquation true focusVar e.Definition |> Equation
       
let solveFor targetVar (eq : Equation) =
    let adjust (eq:Equation) = //move it left collect as polyonmial
        eq - eq.Right
        |> Equation.Apply Algebraic.expand
        |> Equation.ApplyToLeft(fun f ->
                if Polynomial.isPolynomial targetVar f then
                    Polynomial.collectTerms targetVar f
                else f)
    //does the rhs have targetVar in it?
    let eq', adjusted =
        if containsVar targetVar eq.Right then
            adjust eq, true
        else eq, false
    match (reArrangeExprEquation true targetVar eq'.Definition) with
    | Identifier _, r -> [ targetVar <=> r ]
    | e ->
        let peq = if adjusted || eq'.Right = 0Q then eq' else adjust eq'
        if Polynomial.isPolynomial targetVar peq.Left then
            let vals =
                Polynomial.factor targetVar peq.Left
                |> snd
                |> List.map (fun e -> targetVar <=> e)
            match vals with
            | [] -> [Equation e]
            | es -> es
        else [ Equation e ]

let reArrangeInEquality focusVar (e : InEquality) =
    let f,l,r = reArrangeExprInequality true focusVar (e.Left, e.Right) 
    let c' = if f then InEquality.flipComparer e.Comparer else e.Comparer
    InEquality(c', l , r)

let rec invertFunction x expression =
    printfn "%s" (expression |> Infix.format)
    match reArrangeExprEquation false x (expression, x) with
    | Identifier(Symbol _) as y, inv when y = x -> inv
    | _, inv ->
        printfn "Did not completely reduce. Collecting terms"
        printfn "Is it monomial in x?"
        let monom = Polynomial.collectTerms x expression
        if Polynomial.isMonomial x monom then
            printfn "Yes"
            invertFunction x monom
        else
            printfn "no"
            inv


let getCandidates (vset : Hashset<_>) vars knowns =
    knowns
    |> Seq.filter
           (fun (v1, e) ->
           let v1isVar = Expression.isVariable v1
           v1isVar && not (vset.Contains v1)
           && vars |> Seq.exists (fun (v, _) -> e |> containsVar v))

let getSolutions evaluate vset vars candidates =
    [ for (e, e2) in getCandidates vset vars candidates do
          match evaluate vars e2 with
          | None -> ()
          | Some v -> yield e, v ]

let iterativeSolveFilter neq eval vars knowns =
    let vset =
        vars
        |> Seq.map fst
        |> Hashset

    let rec loop cs tsols (vs : seq<_>) =
        let candidates = getCandidates vset vs knowns
        let sols = getSolutions eval vset vs candidates
        match sols with
        | [] ->
            List.concat tsols
            |> List.rev
            |> List.filter (fun (a, b) -> neq a b), List.rev cs
        | sols ->
            sols
            |> List.iter (fst
                          >> vset.Add
                          >> ignore)
            let vars' = sols @ List.ofSeq vs
            loop (List.ofSeq candidates :: cs) (sols :: tsols) vars'

    loop [] [] vars

let iterativeSolve eval vars knowns =
    iterativeSolveFilter (fun _ _ -> true) eval vars knowns

module Units =
    let formatSolved matches newline tx =
        let lookup = dict matches
        tx
        |> List.map (fun (x : Expression, u:Units) ->
            let asunit = 
                match lookup.tryFindIt u.Unit with 
                | Some u' -> (Units.toUnitQuantityValue u' u |> fmt) + space() + u'.AltUnit 
                | _ -> Units.simplifyUnitDesc u

            sprintf "$%s = %s$" (x.ToFormattedString()) asunit)
        |> List.sort
        |> String.concat newline
     
 
//========================
