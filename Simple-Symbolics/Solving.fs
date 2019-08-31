module MathNet.Symbolics.Solving

open MathNet.Symbolics
open Core
open Vars
open Prelude.Common
open MathNet.Symbolics

let reArrangeExprEquationX silent focusVar (left, right) =
    let rec iter fx ops =
        match fx with
        | f when f = focusVar -> f, ops
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
        | Function(Exp, x) ->
            if not silent then printfn "log"
            iter x (ln :: ops)
        | _ -> Undefined, ops //failwith "err"

    let f, ops = iter left []
    f,
    ops
    |> List.rev
    |> List.fold (fun e f -> f e) right
    |> Algebraic.simplify true

let reArrangeExprEquation focusVar (left, right) =
    reArrangeExprEquationX false focusVar (left, right)

let rec invertFunction x expression =
    printfn "%s" (expression |> Infix.format)
    match reArrangeExprEquation x (expression, x) with
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

let quadraticSolve p =
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
        let coeffs = Polynomial.coefficients x p
        let a, b, c = coeffs.[2], coeffs.[1], coeffs.[0]
        Algebraic.simplify true ((-b + sqrt (b ** 2 - 4 * a * c)) / (2 * a)),
        Algebraic.simplify true ((-b - sqrt (b ** 2 - 4 * a * c)) / (2 * a))
    else failwith "Not quadratic"

let completeSquare x p =
    if Polynomial.isPolynomial x p && Polynomial.degree x p = 2Q then
        let coeffs = Polynomial.coefficients x p
        let a, b, c = coeffs.[2], coeffs.[1], coeffs.[0]
        a * (x + b / (2 * a)) ** 2 + c - b ** 2 / (4 * a)
    else failwith "Not quadratic"

let reArrangeEquation focusVar (e : Equation) =
    reArrangeExprEquationX true focusVar e.Definition |> Equation

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

let dispSolvedUnits newline tx =
    tx
    |> List.map
           (fun (x : Expression, u) ->
           sprintf "$%s = %s$" (x.ToFormattedString()) (Units.simplifyUnits u))
    |> List.sort
    |> String.concat newline
