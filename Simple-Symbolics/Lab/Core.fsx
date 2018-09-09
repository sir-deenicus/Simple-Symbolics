
#I @"C:\Users\Admin\Documents\Visual Studio 2017\Libs\MathNet"
#r @".\lib\net461\MathNet.Numerics.dll"
#r @".\lib\net45\MathNet.Numerics.FSharp.dll"
#r @"..\fparsec\net40-client\fparsecCs.dll"
#r @"..\fparsec\net40-client\fparsec.dll"
#r @".\symbolics\net40\mathnet.symbolics.dll"

open MathNet.Symbolics
open System.Numerics
open MathNet.Numerics
open MathNet
open Operators
open MathNet.Symbolics
open MathNet.Symbolics
open MathNet.Symbolics

let flip f a b = f b a

type Expression with
   member t.ToFormattedString() = Infix.format t 
   member t.ToFloat() = (Evaluate.evaluate Map.empty t).RealValue

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
