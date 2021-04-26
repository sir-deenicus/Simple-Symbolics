module MathNet.Symbolics.Trigonometry 

open Prelude.Common 
open Utils
open MathNet.Symbolics.Operators
open MathNet.Numerics
open MathNet.Symbolics
open NumberProperties
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
                     

let rec evalAtan y x =
    let xn, yn = ofRational x, ofRational y
    if x > 0N then arctan (yn / xn)
    elif x < 0N && y >= 0N then Trigonometric.simplify (simplifyWithTable(arctan (yn / xn)) + Pi)
    elif x < 0N && y < 0N then Trigonometric.simplify (simplifyWithTable (arctan (yn / xn)) - Pi)
    elif x = 0N && y > 0N then Pi / 2
    elif x = 0N && y < 0N then -Pi / 2
    else Undefined

and simplifyWithTable =
    function
    | Function (Cos, n) as cosx ->
        TrigTables.cosineLookUp.tryFind n
        |> Option.defaultValue cosx
    | Function (Sin, n) as sinx ->
        TrigTables.sineLookUp.tryFind n
        |> Option.defaultValue sinx
    | Function (Tan, n) as tanx ->
        TrigTables.tanLookUp.tryFind n
        |> Option.defaultValue tanx
    | Function (Atan, x) as atanx ->
        TrigTables.aTanLookUp.tryFind x
        |> Option.defaultValue atanx
    | FunctionN (Atan, [ a; b ]) as atanx ->
        match a, b with
        | Number x, Number y ->
            let atanx' = evalAtan x y
            atanx'
            |> TrigTables.aTanLookUp.tryFind
            |> Option.defaultValue atanx'
        | _ -> atanx
    | x -> x 

let x = symbol "x"
let a = symbol "a"
let b = symbol "b"

let TrigEqualities =
    [ tan x <=> sin x / cos x
      cot x <=> 1 / tan x
      sec x <=> 1 / cos x
      csc x <=> 1 / sin x
      (sin x) ** 2 + (cos x) ** 2 <=> 1Q
      cos x <=> sin (Pi / 2 - x)
      sin x <=> cos (Pi / 2 - x)
      sin (2 * x) <=> 2 * sin x * cos x
      cos (2 * x) <=> (cos x) ** 2 - (sin x) ** 2
      sin (a + b) <=> sin a * cos b + cos a * sin b
      sin (a - b) <=> sin a * cos b - cos a * sin b
      cos (a + b) <=> cos a * cos b - sin a * sin b
      cos (a - b) <=> cos a * cos b + sin a * sin b ]