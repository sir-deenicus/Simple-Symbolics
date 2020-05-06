module MathNet.Symbolics.Trigonometry 

open Prelude.Common 
open Utils
open MathNet.Symbolics.Operators
open MathNet.Numerics
open MathNet.Symbolics
open NumberTheory
open Equations

let Pi = Constants.pi

let isTrigonometricFunction = function
    | Function.Cos
    | Function.Sin
    | Function.Tan
    | Function.Sec
    | Function.Cot
    | Function.Acos
    | Function.Asin
    | Function.Atan 
    | Function.Asec
    | Function.Acot-> true 
    | _ -> false


module TrigTables = 

    let internal take3 xs = xs |> List.tail |> List.take 3 

    let angles =
        [ 0Q; Constants.pi / 6Q; Constants.pi / 4Q; Constants.pi / 3Q; 
          Constants.pi / 2Q; Constants.pi; 3 * Constants.pi / 2Q; 2 * Constants.pi ]

    let cosineVals = [ 1Q; sqrt(3Q)/2; sqrt(2Q)/2; 1/2Q; 0Q; -1Q; 0Q; 1Q ]
    
    let sineVals   = [ 0Q; 1/2Q; sqrt(2Q)/2; sqrt(3Q)/2; 1Q; 0Q; -1Q; 0Q ]
    
    let tanVals    = [ 0Q; sqrt(3Q)/3; 1Q; sqrt 3Q; undefined; 0Q; undefined; 0Q ]

    let angles2 =
        angles |> take3 |> List.map (fun a -> Pi / 2 + (Pi / 2Q - a))

    let angles3 =
        angles |> take3 |> List.map ((+) Pi)

    let angles4 =
        angles3 |> List.map (fun a -> 3 * Pi / 2 + (3 * Pi / 2Q - a))

    let costable2 =
        List.zip angles2 (List.map ((*) -1) (take3 cosineVals))

    let costable3 =
        List.zip angles3 (List.map ((*) -1) (take3 cosineVals))

    let costable4 = List.zip angles4 (take3 cosineVals)

    let sintable2 = List.zip angles2 (take3 sineVals)

    let sintable3 =
        List.zip angles3 (List.map ((*) -1) (take3 sineVals))

    let sintable4 =
        List.zip angles4 (List.map ((*) -1) (take3 sineVals))

    let cosineLookUp =
        Dict.ofSeq (List.zip angles cosineVals @ costable2 @ costable3 @ costable4)

    let sineLookUp =
        Dict.ofSeq (List.zip angles sineVals @ sintable2 @ sintable3 @ sintable4)

    let tanLookUp = Dict.ofSeq (List.zip angles tanVals)

    let aTanLookUp =
        Dict.ofSeq [ -sqrt (3Q), -Pi / 3
                     -1Q, -Pi / 4
                     -1 / sqrt (3Q), -Pi / 6
                     0Q, 0Q
                     1 / sqrt (3Q), Pi / 6
                     1Q, Pi / 4
                     sqrt 3Q, Pi / 3 ]
                     

let evalAtan y x = 
    let xn, yn = rational x, rational y
    if x > 0N then arctan (yn / xn)
    elif x < 0N && y >= 0N then Trigonometric.simplify (arctan (yn / xn) + Pi)
    elif x < 0N && y < 0N then Trigonometric.simplify (arctan (yn / xn) - Pi)
    elif x = 0N && y > 0N then Pi / 2
    elif x = 0N && y < 0N then -Pi / 2
    else Undefined

let simplifyTrigTerm = function
    | Function(Cos, n) as cosx ->
        TrigTables.cosineLookUp.tryFind n
        |> Option.defaultValue cosx
    | Function(Sin, n) as sinx ->
        TrigTables.sineLookUp.tryFind n
        |> Option.defaultValue sinx   
    | Function(Tan, n) as tanx ->
        TrigTables.tanLookUp.tryFind n
        |> Option.defaultValue tanx 
    | Function(Atan, x) as atanx ->
        TrigTables.aTanLookUp.tryFind x
        |> Option.defaultValue atanx   
    | FunctionN(Atan, [a;b]) as atanx  -> 
        match a,b with 
        | Number x, Number y -> 
            let atanx' = evalAtan x y
            atanx'
            |> TrigTables.aTanLookUp.tryFind
            |> Option.defaultValue atanx'
        | _ -> atanx        
    | x -> x      

let doubleAngleIdentity2a = function
    | Function(Cos, Product[n; x]) when n = 2Q -> 2 * (cos x) ** 2 - 1
    | f -> f
     
let (|IsSin|_|) = function
      | Function(Sin,e) -> Some e
      | _ -> None 

let (|IsCos|_|) = function
      | Function(Cos,e) -> Some e
      | _ -> None 

let (|IsTan|_|) = function
      | Function(Tan,e) -> Some e
      | _ -> None 

let (|IsCot|_|) = function
      | Function(Cot,e) -> Some e
      | _ -> None 

let (|IsSec|_|) = function
      | Function(Sec,e) -> Some e
      | _ -> None 

let (|IsCsc|_|) = function
      | Function(Csc,e) -> Some e
      | _ -> None  

let tanToSinCos = function 
    | IsTan a -> sin a / cos a
    | x -> x

let cotToTan = function 
    | IsCot a -> 1 / tan a
    | x -> x

let secToCos = function 
    | IsSec a -> 1 / cos a
    | x -> x

let cscToSin = function 
    | IsCsc a -> 1 / sin a
    | x -> x


module SumDifferenceRule =
    let sin =
        function 
        | IsSin(Sum[a;b]) -> sin a * cos b + cos a * sin b
        | IsSin(Minus(a,b)) -> sin a * cos b - cos a * sin b
        | Sum [Product [IsSin a; IsCos b] ; Product [IsCos a2; IsSin b2]] 
            when a = a2 && b = b2 ->  sin (a + b)
        | Minus(Product [IsSin a; IsCos b] , Product [IsCos a2; IsSin b2]) 
            when a = a2 && b = b2 -> sin (a - b)
        | x -> x

    let cos =
        function 
        | IsCos(Sum[a;b]) -> cos a * cos b - sin a * sin b
        | IsCos(Minus(a,b)) -> cos a * cos b + sin a * sin b
        | Minus (Product [IsCos a; IsCos b], Product [IsSin a2; IsSin b2])
            when a = a2 && b = b2 ->  cos (a + b)
        | Sum [Product [IsCos a; IsCos b] ; Product [IsSin a2; IsSin b2]]
            when a = a2 && b = b2 -> cos (a - b)
        | x -> x 

module DoubleAngle =
    let sin =
        function 
        | IsSin (Product [Two; x]) -> 2 * sin x * cos x
        | Product [Two; IsSin x ;IsCos x2 ] when x = x2 -> sin (2*x) 
        | x -> x

let cosToSin = function 
    | IsCos(x) -> sin (Pi/2 - x)
    | x -> x

let sinToCos = function 
    | IsSin(x) -> cos (Pi/2 - x)
    | x -> x

let x = symbol "x"
let a = symbol "a"
let b = symbol "b"

let Equalities = 
    [tan x <=> sin x/ cos x; 
     cot x <=> 1 / tan x; sec x <=> 1/ cos x; csc x <=> 1/ sin x; (sin x) ** 2 + (cos x)**2 <=> 1Q 
     ]