module MathNet.Symbolics.Trigonometry

open Prelude.Common
open Utils
open MathNet.Symbolics.Operators
open MathNet.Numerics
open MathNet.Symbolics
open NumberProperties
open Equations

let Pi = Constants.pi

let isTrigonometricFunction =
    function
    | Function.Cos
    | Function.Sin
    | Function.Tan
    | Function.Sec
    | Function.Cot
    | Function.Acos
    | Function.Asin
    | Function.Atan
    | Function.Asec
    | Function.Acot -> true
    | _ -> false

let (|IsSin|_|) =
    function
    | Function(Sin, e) -> Some e
    | _ -> None

let (|IsCos|_|) =
    function
    | Function(Cos, e) -> Some e
    | _ -> None

let (|IsTan|_|) =
    function
    | Function(Tan, e) -> Some e
    | _ -> None

let (|IsCot|_|) =
    function
    | Function(Cot, e) -> Some e
    | _ -> None

let (|IsSec|_|) =
    function
    | Function(Sec, e) -> Some e
    | _ -> None

let (|IsCsc|_|) =
    function
    | Function(Csc, e) -> Some e
    | _ -> None

module TrigTables =

    let internal take3 xs = xs |> List.tail |> List.take 3

    let angles =
        [ 0Q
          Constants.pi / 6Q
          Constants.pi / 4Q
          Constants.pi / 3Q
          Constants.pi / 2Q
          Constants.pi
          3 * Constants.pi / 2Q
          2 * Constants.pi ]

    let cosineVals = [ 1Q; sqrt (3Q) / 2; sqrt (2Q) / 2; 1 / 2Q; 0Q; -1Q; 0Q; 1Q ]

    let sineVals = [ 0Q; 1 / 2Q; sqrt (2Q) / 2; sqrt (3Q) / 2; 1Q; 0Q; -1Q; 0Q ]

    let tanVals = [ 0Q; sqrt (3Q) / 3; 1Q; sqrt 3Q; undefined; 0Q; undefined; 0Q ]

    let angles2 = angles |> take3 |> List.map (fun a -> Pi / 2 + (Pi / 2Q - a))

    let angles3 = angles |> take3 |> List.map ((+) Pi)

    let angles4 = angles3 |> List.map (fun a -> 3 * Pi / 2 + (3 * Pi / 2Q - a))

    let costable2 = List.zip angles2 (List.map ((*) -1) (take3 cosineVals))

    let costable3 = List.zip angles3 (List.map ((*) -1) (take3 cosineVals))

    let costable4 = List.zip angles4 (take3 cosineVals)

    let sintable2 = List.zip angles2 (take3 sineVals)

    let sintable3 = List.zip angles3 (List.map ((*) -1) (take3 sineVals))

    let sintable4 = List.zip angles4 (List.map ((*) -1) (take3 sineVals))

    let cosineLookUp =
        Dict.ofSeq (List.zip angles cosineVals @ costable2 @ costable3 @ costable4)

    let sineLookUp =
        Dict.ofSeq (List.zip angles sineVals @ sintable2 @ sintable3 @ sintable4)

    let tanLookUp = Dict.ofSeq (List.zip angles tanVals)

    let aTanLookUp =
        Dict.ofSeq
            [ -sqrt(3Q), -Pi / 3
              -1Q, -Pi / 4
              -1 / sqrt (3Q), -Pi / 6
              0Q, 0Q
              1 / sqrt (3Q), Pi / 6
              1Q, Pi / 4
              sqrt 3Q, Pi / 3 ]


let rec evalAtan y x =
    let xn, yn = ofRational x, ofRational y

    if x > 0N then
        arctan (yn / xn)
    elif x < 0N && y >= 0N then
        Trigonometric.simplify (simplifyWithTable (arctan (yn / xn)) + Pi)
    elif x < 0N && y < 0N then
        Trigonometric.simplify (simplifyWithTable (arctan (yn / xn)) - Pi)
    elif x = 0N && y > 0N then
        Pi / 2
    elif x = 0N && y < 0N then
        -Pi / 2
    else
        Undefined

and simplifyWithTable =
    function
    | Function(Cos, n) as cosx -> TrigTables.cosineLookUp.tryFind n |> Option.defaultValue cosx
    | Function(Sin, n) as sinx -> TrigTables.sineLookUp.tryFind n |> Option.defaultValue sinx
    | Function(Tan, n) as tanx -> TrigTables.tanLookUp.tryFind n |> Option.defaultValue tanx
    | Function(Atan, x) as atanx -> TrigTables.aTanLookUp.tryFind x |> Option.defaultValue atanx
    | FunctionN(Atan, [ a; b ]) as atanx ->
        match a, b with
        | Number x, Number y ->
            let atanx' = evalAtan x y
            atanx' |> TrigTables.aTanLookUp.tryFind |> Option.defaultValue atanx'
        | _ -> atanx
    | x -> x

let simplify x =
    simplifyWithTable (Trigonometric.simplify x)

let x = symbol "x"
let y = symbol "y"
let a = symbol "a"
let b = symbol "b"

let TrigEqualities =
    [ tan x <=> sin x / cos x
      cot x <=> 1 / tan x
      sec x <=> 1 / cos x
      csc x <=> 1 / sin x
      (sin x) ** 2 + (cos x) ** 2 <=> 1Q
      (tan x) ** 2 + 1 <=> (sec x) ** 2
      cos x <=> sin (Pi / 2 - x)
      sin x <=> cos (Pi / 2 - x)
      sin (2 * x) <=> 2 * sin x * cos x      
      cos (2 * x) <=> (cos x) ** 2 - (sin x) ** 2
      tan (2 * x) <=> (2 * tan x) / (1 - (tan x) ** 2)
      2 * sin x * cos x <=> (2 * tan x) / (1 + (tan x) ** 2)
      sin x * cos y <=> (sin (x + y) + sin (x - y)) / 2
      cos x * sin y <=> (sin (x + y) - sin (x - y)) / 2
      cos x * cos y <=> (cos (x + y) + cos (x - y)) / 2
      sin x * sin y <=> (cos (x - y) - cos (x + y)) / 2
      sin (a + b) <=> sin a * cos b + cos a * sin b
      sin (a - b) <=> sin a * cos b - cos a * sin b
      cos (a + b) <=> cos a * cos b - sin a * sin b
      cos (a - b) <=> cos a * cos b + sin a * sin b 
      tan (a + b) <=> (tan a + tan b) / (1 - tan a * tan b)
      tan (a - b) <=> (tan a - tan b) / (1 + tan a * tan b)]

let applyTrigEquality =
    function
    | Function(Tan, x) -> sin x / cos x
    | Divide(Function(Sin, x), Function(Cos, _)) -> tan x
    | Function(Cot, x) -> 1 / tan x
    | Divide(Number n, Function(Tan, x)) when n = 1N -> cot x
    | Function(Sec, x) -> 1 / cos x
    | Divide(Number n, Function(Cos, x)) when n = 1N -> sec x
    | Function(Csc, x) -> 1 / sin x
    | Divide(Number n, Function(Sin, x)) when n = 1N -> csc x
    | Sum [ Power(Function(Sin, _), Number n); Power(Function(Cos, _), Number m) ] when n = 2N && m = 2N -> 1Q
    | Sum [ Power(Function(Cos, _), Number n); Power(Function(Sin, _), Number m) ] when n = 2N && m = 2N -> 1Q
    | Power(Function(Tan, x), Number n) when n = 2N -> (sec x) ** 2 - 1
    | Power(Function(Sec, x), Number n) when n = 2N -> (tan x) ** 2 + 1
    | Function(Cos, x) -> sin (Pi / 2 - x)
    | Function(Sin, x) -> cos (Pi / 2 - x)
    | Function(Sin, Product [ Number n; x ]) when n = 2N -> 2 * sin x * cos x
    | Function(Cos, Product [ Number n; x ]) when n = 2N -> (cos x) ** 2 - (sin x) ** 2
    | Function(Tan, Product [ Number n; x ]) when n = 2N -> (2 * tan x) / (1 - (tan x) ** 2)
    | Product [ Number n; Function(Sin, x); Function(Cos, y) ] when n = 2N && x = y -> (2 * tan x) / (1 + (tan x) ** 2)
    | Product [Function (Sin, x); Function (Cos, y)] -> (sin (x + y) + sin (x - y)) / 2
    | Product [Function (Cos, x); Function (Sin, y)] -> (sin (x + y) - sin (x - y)) / 2
    | Product [Function (Cos, x); Function (Cos, y)] -> (cos (x + y) + cos (x - y)) / 2
    | Product [Function (Sin, x); Function (Sin, y)] -> (cos (x - y) - cos (x + y)) / 2
    | Function(Sin, Sum [ a; b ]) -> sin a * cos b + cos a * sin b
    | Function(Sin, Minus(a, b)) -> sin a * cos b - cos a * sin b
    | Function(Cos, Sum [ a; b ]) -> cos a * cos b - sin a * sin b
    | Function(Cos, Minus(a, b)) -> cos a * cos b + sin a * sin b
    | Function(Tan, Sum [ a; b ]) -> (tan a + tan b) / (1 - tan a * tan b)
    | Function(Tan, Minus(a, b)) -> (tan a - tan b) / (1 + tan a * tan b)
    | x -> x

        
module TrigEqualities = 
    let tanToSinCos = function 
        | Function(Tan, x) -> sin x / cos x
        | x -> x
    
    let sinCosToTan = function
        | Divide(Function(Sin, x), Function(Cos, _)) -> tan x
        | x -> x

    let cotToTan = function
        | Function(Cot, x) -> 1 / tan x
        | x -> x

    let tanToCot = function
        | Divide(Number n, Function(Tan, x)) when n = 1N -> cot x
        | x -> x

    let secToCos = function
        | Function(Sec, x) -> 1 / cos x
        | x -> x

    let cosToSec = function
        | Divide(Number n, Function(Cos, x)) when n = 1N -> sec x
        | x -> x

    let cscToSin = function
        | Function(Csc, x) -> 1 / sin x
        | x -> x

    let sinToCsc = function
        | Divide(Number n, Function(Sin, x)) when n = 1N -> csc x
        | x -> x

    let pythagoreanIdentity = function
        | Sum [ Power(Function(Sin, x), Number n); Power(Function(Cos, y), Number m) ] when n = 2N && m = 2N -> 1Q
        | Sum [ Power(Function(Cos, x), Number n); Power(Function(Sin, y), Number m) ] when n = 2N && m = 2N -> 1Q
        | x -> x

    let pythagoreanIdentityTan = function
        | Power(Function(Tan, x), Number n) when n = 2N -> (sec x) ** 2 - 1
        | x -> x

    let pythagoreanIdentitySec = function
        | Power(Function(Sec, x), Number n) when n = 2N -> (tan x) ** 2 + 1
        | x -> x

    let cosToSin = function
        | Function(Cos, x) -> sin (Pi / 2 - x)
        | x -> x

    let sinToCos = function
        | Function(Sin, x) -> cos (Pi / 2 - x)
        | x -> x

    let doubleAngleSin = function
        | Function(Sin, Product [ Number n; x ]) when n = 2N -> 2 * sin x * cos x
        | x -> x

    let doubleAngleCos = function
        | Function(Cos, Product [ Number n; x ]) when n = 2N -> (cos x) ** 2 - (sin x) ** 2
        | x -> x

    let doubleAngleSinTan = function
        | Product [ Number n; Function(Sin, x); Function(Cos, y) ] when n = 2N && x = y -> (2 * tan x) / (1 + (tan x) ** 2)
        | x -> x

    let productRuleSinCos = function
        | Product [Function (Sin, x); Function (Cos, y)] -> (sin (x + y) + sin (x - y)) / 2
        | x -> x

    let productRuleCosSin = function
        | Product [Function (Cos, x); Function (Sin, y)] -> (sin (x + y) - sin (x - y)) / 2
        | x -> x

    let productRuleCosCos = function
        | Product [Function (Cos, x); Function (Cos, y)] -> (cos (x + y) + cos (x - y)) / 2
        | x -> x

    let productRuleSinSin = function
        | Product [Function (Sin, x); Function (Sin, y)] -> (cos (x - y) - cos (x + y)) / 2
        | x -> x

    let sinAddition = function
        | Function(Sin, Sum [ a; b ]) -> sin a * cos b + cos a * sin b
        | x -> x

    let sinSubtraction = function
        | Function(Sin, Minus(a, b)) -> sin a * cos b - cos a * sin b
        | x -> x

    let cosAddition = function
        | Function(Cos, Sum [ a; b ]) -> cos a * cos b - sin a * sin b
        | x -> x

    let cosSubtraction = function   
        | Function(Cos, Minus(a, b)) -> cos a * cos b + sin a * sin b
        | x -> x

    let tanAddition = function
        | Function(Tan, Sum [ a; b ]) -> (tan a + tan b) / (1 - tan a * tan b)
        | x -> x

    let tanSubtraction = function
        | Function(Tan, Minus(a, b)) -> (tan a - tan b) / (1 + tan a * tan b)
        | x -> x
         




