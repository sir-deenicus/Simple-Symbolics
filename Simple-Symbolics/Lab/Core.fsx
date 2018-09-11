﻿
#I @"C:\Users\Admin\Documents\Visual Studio 2017\Libs\MathNet"
#r @".\lib\net461\MathNet.Numerics.dll"
#r @".\lib\net45\MathNet.Numerics.FSharp.dll"
#r @"..\fparsec\net40-client\fparsecCs.dll"
#r @"..\fparsec\net40-client\fparsec.dll"
#r @".\symbolics\net40\mathnet.symbolics.dll"

open MathNet.Symbolics  
open Operators 
open MathNet.Numerics

let flip f a b = f b a

let standardSymbols = Map ["π", FloatingPoint.Real System.Math.PI]

module Algebraic =
  let rec simplify = function 
     | Power (Power (x, a), b) -> simplify(Power(simplify x, simplify (a * b)))
     | Power (x, a) when a = 1Q -> x
     | x -> x


type Expression with
   member t.ToFormattedString() = Infix.format t 
   member t.ToFloat() = (Evaluate.evaluate standardSymbols t).RealValue

type Complex(r:Expression,i:Expression) =  
  member __.Real = r
  member __.Imaginary = i

  member __.Conjugate = Complex(r, -i)

  member __.Magnitude = sqrt (r**2 + i**2)

  member __.Phase =
     let x,y = r.ToFloat(), i.ToFloat()
     if  x > 0. then arctan (i/r) 
     elif x < 0. && y >= 0. then Trigonometric.simplify (arctan (i/r) + pi)
     elif x < 0. && y < 0. then Trigonometric.simplify (arctan (i/r) - pi)
     elif x = 0. && y > 0. then pi/2
     elif x = 0. && y < 0. then -pi/2
     else Undefined

  static member Zero = Complex(0Q, 0Q)

  static member (+) (a:Complex,b:Complex) = Complex(a.Real + b.Real, a.Imaginary + b.Imaginary)

  static member (-) (a:Complex,b:Complex) = Complex(a.Real - b.Real, a.Imaginary - b.Imaginary)

  static member (*) (a:Complex,b:Complex) = 
    Complex(a.Real * b.Real - a.Imaginary * b.Imaginary, a.Imaginary * b.Real + a.Real * b.Imaginary)

  static member (*) (a:Complex,b:Expression) = 
    Complex(a.Real * b, a.Imaginary * b)

  static member (*) (a:Expression,b:Complex) = 
    Complex(a * b.Real, a * b.Imaginary)
  static member (/) (a:Complex, b:Expression) = Complex( a.Real / b, a.Imaginary / b)

  static member (/) (a:Complex, b:Complex) = let conj = b.Conjugate in (a * conj) / (b * conj).Real 

  static member (/) (a:Expression, b:Complex) = (Complex a) / b

  new(r) = Complex(r, 0Q)

  override t.ToString() = sprintf "(%s, %s)" (Infix.format t.Real) (Infix.format t.Imaginary)  


type Units(q:Expression,u:Expression, ?altUnit) =
  let mutable altunit = defaultArg altUnit ("")
  static member numstr = function | Number(x) when x = 1000N -> "kilo" 
                                  | Number(x) when x = 1000_000N -> "mega"
                                  | Number(x) when x = 1_000_000_000N -> "giga"
                                  | Number(x) when x = 1_000_000_000_000N -> "tera"
                                  | Number x when x = 1N -> ""
                                  | x -> x.ToFormattedString()
  member __.Quantity = q
  member __.Unit = u 
  member __.AltUnit with get() = altunit and set u = altunit <- u
  static member Zero = Units(0Q, 0Q)
  static member (+) (a:Units,b:Units) = 
    if a.Unit = b.Unit then
      Units(a.Quantity + b.Quantity, a.Unit, a.AltUnit)    
    elif b.Unit = 0Q then Units(a.Quantity, a.Unit, a.AltUnit)
    elif a.Unit = 0Q then Units(b.Quantity, b.Unit, b.AltUnit)
    else failwith "Units don't match"
  static member (-) (a:Units,b:Units) = a + -1 * b   
  static member (*) (a:Units,b:Units) =  
    Units(a.Quantity * b.Quantity, a.Unit * b.Unit, a.AltUnit + " " + b.AltUnit)
  static member (*) (a:Units,b:Expression) = Units(a.Quantity * b, a.Unit, a.AltUnit)
  static member (*) (a:Units,b:int) = Units(a.Quantity * b, a.Unit, a.AltUnit)
  static member (*) (a:int,b:Units) = Expression.FromInt32 a * b
  static member (*) (a:Expression,b:Units) = 
    Units(a * b.Quantity, b.Unit
         , Units.numstr a + (if b.AltUnit = "" then b.Unit.ToFormattedString() else b.AltUnit))
  static member Pow (a:Units,b:int) = 
    Units(a.Quantity ** b, a.Unit ** b, a.AltUnit + "^"+string b )
  static member Pow (a:Units,b:Expression) = 
    Units(Algebraic.simplify (a.Quantity ** b), Algebraic.simplify (a.Unit ** b))  
  static member (/) (a:Units, b:Expression) = Units( a.Quantity / b, a.Unit, a.AltUnit)
  static member (/) (a:Units, b:Units) = Units(a.Quantity / b.Quantity, a.Unit / b.Unit, a.AltUnit + "/" + b.AltUnit)
  static member (/) (a:Expression, b:Units) = Units(a / b.Quantity, 1 / b.Unit, b.AltUnit + "^-1") 
  static member To (a:Units, b:Units) = 
      if a.Unit = b.Unit then 
         let altunit = if b.AltUnit = "" then 
                         Units.numstr b.Quantity + " " + b.Unit.ToFormattedString() 
                       else b.AltUnit
         Some (sprintf "%s %s" ((a / b).Quantity.ToFormattedString()) altunit ) 
      else None 
  static member To (a:Units, b:Units,unitstr) = if a.Unit = b.Unit then Some (sprintf "%s %s" ((a / b).Quantity.ToFormattedString()) unitstr ) else None 

  override t.ToString() = sprintf "(%s, %s)" (Infix.format t.Quantity) (Infix.format t.Unit)  

module Units =
  let (^) a b = Units(a,b)
  let setAlt alt (u:Units) = u.AltUnit <- alt; u
   

  let kg = Units(1Q, Operators.symbol "kg", "kg")
  let meter = Units(1Q, Operators.symbol "meters", "meter")
  let sec = Units(1Q, Operators.symbol "sec", "sec")

  let flops = Units(1Q, Operators.symbol "flops")
  let bits = Units(1Q, Operators.symbol "bits")
  let bytes = 8Q * bits |> setAlt "bytes"
   
  let N = kg * meter / sec ** 2 |> setAlt "N" 
  let J = kg * meter ** 2 * sec ** -2 |> setAlt "J"   
  let km = 1000Q * meter

  let W = J / sec  |> setAlt "W"
  let kilo = 1000Q
  let mega = 1_000_000Q
  let giga = 1_000_000_000Q
  let tera = 1_000_000_000_000Q
  let minute = 60Q * sec |> setAlt "minute"
  let hr = 60Q * minute |> setAlt "hr"
  
  let differentiate (dy:Units) (dx:Units) =
      Units(Calculus.differentiate dy.Quantity dx.Quantity, dx.Unit/dy.Unit, dx.AltUnit+"/"+dy.AltUnit)

  let units = [W, "Power";J, "Energy";N,"Force"; hr, "Time"; sec, "Time"; kg, "mass";meter, "length"]

  let simplifyUnits (u:Units) = 
      List.filter (fun (um:Units, _) -> u.Unit = um.Unit) units
      |> List.map (fun (u',t) -> Units.To(u, u') |> Option.map (fun s -> s + " (" + t + ")")) 
      |> List.minBy (fun u -> Option.get u |> String.length)


let rec containsVar x = function
   | Identifier _ as sy when sy = x -> true
   | Power(Identifier (Symbol _) as sy, _) when sy = x -> true
   | Function(_, (Identifier (Symbol _ ) as sy)) when sy = x -> true
   | Power(Function(_, (Identifier (Symbol _) as sy)), _) when sy = x -> true   
   | Power(Identifier (Symbol _ ) as sy, _) when sy = x -> true
   | Power(Sum l, _)  -> List.exists (containsVar x) l
   | Power(Product l, _)  -> List.exists (containsVar x) l
   | Product l -> List.exists (containsVar x) l
   | Sum l -> List.exists (containsVar x) l
   | _ -> false


module Vars =
  let a = symbol "a"
  let b = symbol "b"
  let c = symbol "c"
  let d = symbol "d"
  let r = symbol "r"
  let t = symbol "t"
  let u = symbol "u"
  let v = symbol "v"
  let x = symbol "x"
  let y = symbol "y"
  let z = symbol "z"

  let y1 = symbol "y₁"
  let y2 = symbol "y₂"
  let x1 = symbol "x₁"
  let x2 = symbol "x₂"
  let x3 = symbol "x₃"

  let phi = symbol "φ"  
  let pi = symbol "π"
  let π = symbol "π"
