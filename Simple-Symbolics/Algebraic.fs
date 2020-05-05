namespace MathNet.Symbolics

open Prelude.Common
open Core
open MathNet.Numerics

module Rational =
    let reciprocal e = 
        Rational.denominator e / Rational.numerator e 

    let cancelDivision =
        let getNegProducts =
            function
            | Power(Identifier(Symbol _) as v, _) -> [ v ]
            | Power(Product l, _) -> List.filter Expression.isVariable l
            | _ -> []

        let getPosProducts =
            function
            | Identifier(Symbol _) as v -> [ v ]
            | Product _ as p ->
                p
                |> Expression.simplifyLite
                |> Structure.toList
                |> List.filter Expression.isVariable
            | _ -> []

        let filterProducts f =
            function
            | Identifier(Symbol _) as v ->
                if f v then v
                else 1Q
            | Power(Identifier(Symbol _) as v, _) as p ->
                if f v then p
                else 1Q
            | Power(Product l, n) -> Power(Product(List.filter f l), n)
            | Product _ as p ->
                p
                |> Expression.simplifyLite
                |> Structure.toList
                |> List.filter f
                |> Product
            | e -> e

        function
        | Product l ->
            let negs, others = List.partition Expression.isNegativePower l
            let cancelset = List.collect getNegProducts negs |> Hashset
            let posset = List.collect (getPosProducts) others
            cancelset.IntersectWith posset
            Product(List.map (filterProducts (cancelset.Contains >> not)) l)
        | f -> f


module Algebraic =
    open Core
    open NumberTheory
    let groupInSumWith var = function
        | Sum l -> 
            let haves, nots = List.partition (Expression.containsExpression var) l
            Product[var; haves |> List.sumBy (fun x -> x/var)] + Sum nots
        | f -> f 
    let multiplyAsUnityBy m = function
        | Product (Power(x,n)::rest) ->
            Product (m::Power(Algebraic.expand (x*m),n)::rest)
        | Power(x, n) ->
            Product[m;Power(Algebraic.expand (x*m),n)]        
        | Product l as p -> 
            let parted =
                List.partition (function | Power(_,_) -> true | _ -> false) l
            match parted with
            | [Power(x,n)], rest -> 
                Product (m::Power(Algebraic.expand (x*m),n)::rest)
            | _ -> p
        | f -> f
 
    let dividesHeuristic a b = Structure.width (a / b) < Structure.width a

    let consolidateSumsBy chooser = function
        | Sum l as s ->
            let exprlist = List.toArray l

            let divides =
                [| for i in 0..exprlist.Length - 2 do
                       for j in i + 1..exprlist.Length - 1 do
                           let d = (exprlist.[i] / exprlist.[j])

                           let xr =
                               exprlist.[i] / Rational.numerator d
                               |> abs
                               |> Expression.cancelAbs
                           if xr <> 1Q then yield xr |]
                |> Hashset
                |> Seq.toArray
            if divides.Length = 0 then s 
            else
                let divisor = chooser divides

                let divisibles, undivisible =
                    exprlist
                    |> Array.groupBy (fun x -> Rational.denominator (x / divisor) = 1Q)
                    |> Array.partition fst

                let divided = 
                    divisibles.[0]
                    |> snd
                    |> Array.map (fun x -> x / divisor)
                    |> List.ofArray
                    |> Sum
                let nondivisibles = if undivisible.Length = 0 then 0Q else Sum (List.ofArray (snd undivisible.[0])) 
                divisor * divided + nondivisibles            
        | x -> x 

    let consolidateSums = consolidateSumsBy (Array.maxBy Structure.width)

    let intersectAll l =
        let getNumber =
            function
            | Product(Number n :: _) -> abs n
            | Number n -> abs n
            | _ -> 1N

        let curset = Hashset(List.head l |> Structure.listOfProduct)

        let rec loop (cnum : BigRational) =
            function
            | Product ps :: rest ->
                let num' =
                    if cnum = 1N then 1N
                    elif not cnum.IsInteger then
                        if getNumber (Product ps) = cnum then cnum
                        else 1N
                    else gcd (getNumber (Product ps)) cnum
                curset.IntersectWith ps
                if curset.Count = 0 && num' = 1N then [], 1N
                else loop num' rest
            | Number n :: rest when cnum <> 1N ->
                let num' =
                    if not cnum.IsInteger then
                        if n = cnum then cnum
                        else 1N
                    else gcd n cnum
                if curset.Count = 0 && num' = 1N then [], 1N
                else loop num' rest
            | f :: rest ->
                curset.IntersectWith [ f ]
                if curset.Count = 0 then [], 1N
                else loop 1N rest
            | [] -> Seq.toList curset, cnum
        loop (getNumber (List.head l)) (List.tail l)

    let consolidateSums2 =
        function
        | Sum l as s ->
            match intersectAll l with
            | [], n ->
                if n <> 1N then
                    let p = Expression.FromRational n
                    Product [ p; s / p |> Algebraic.expand ]
                else s
            | [ Number _ ], n ->
                if n = 1N then s
                else
                    let p = Number n
                    Product [ p; s / p |> Algebraic.expand ]
            | [ factor ], n ->
                let p =
                    if n = 1N then factor
                    else Product [ Number n; factor ]
                Product [ p; s / p |> Algebraic.expand ]
            | product, n ->
                let p =
                    Product
                        (if n = 1N then product
                         else
                             Number n
                             :: (List.filter
                                     (Expression.isRationalNumber >> not)
                                     product))
                Product [ p ; s / p |> Algebraic.expand ]
        | f -> f

    let intersectAllSimple l =
        let curset = Hashset(List.head l |> Structure.listOfProduct) 
        let rec loop = function
             | Product ps::rest ->
                curset.IntersectWith ps
                if curset.Count = 0 then [] else loop rest
             | f::rest -> 
                curset.IntersectWith [f]
                if curset.Count = 0 then [] else loop rest
             | [] -> Seq.toList curset
        loop (List.tail l)

    let internal consolidateSumsSimpleGen f = 
        function
        | Sum l as s -> 
            match intersectAllSimple l with
            | [] -> s
            | [factor] ->  
                Product[factor ; f factor s ]
            | product -> 
                let p = Product product
                Product[p ; f p s ] 
        | f -> f
    
    let consolidateSumsSimple =
        consolidateSumsSimpleGen (fun p s -> Algebraic.expand (s / p))

    //let consolidateSumsSimple2 = consolidateSumsSimpleGen Expression.groupInSumWith
     
