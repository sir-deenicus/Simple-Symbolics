module MathNet.Symbolics.Extras

open MathNet.Symbolics.Operators
open MathNet.Numerics
open System

let flip f a b = f b a

let standardSymbols = Map []

let mutable expressionFormater = Infix.format

module BigRational =    
  open Microsoft.FSharp.Core.Operators
  ///limited by range of decimal (which is used as a less noisy alternative to floats)
  let fromFloat (f:float) =
      let df = decimal f
      if df = floor df then BigRational.FromBigInt (Numerics.BigInteger df)
      else
        let s = string (df - floor df)
        let pow10 = Numerics.BigInteger 10 ** (s.Length - 2)
        BigRational.FromBigIntFraction(Numerics.BigInteger(df * decimal pow10), pow10)
  let fromFloatRepeating (f:float) =
      let df = decimal f
      let len = float((string (df - floor df)).Length - 2)
      let pow10 = decimal (10. ** len)
      if abs f < 1. then
        BigRational.FromIntFraction(int (df * pow10), int (floor (pow10 - df)))
      else BigRational.FromIntFraction(int (df * pow10 - floor df), int (pow10 - 1M))
 
module Algebraic = 
  let simplify simplifysqrt fx =
      let rec simplifyLoop = function               
         | Power (x, Number n) when n = 1N -> simplifyLoop x
         | Power (Number x, _) when x = 1N -> 1Q  
         | Power (Product[x], n) 
         | Power (Sum[x], n) -> simplifyLoop (Power(x, n))
         | Power (Power (x, a), b) -> simplifyLoop(Power(x, (a * b)))
         | Power (x,n) when n = 1Q/2Q && simplifysqrt -> 
             match None with
             | Some x' -> x'  
             | None -> Power(simplifyLoop x, n)
         | Power (x,n) -> Power(simplifyLoop x, simplifyLoop n) 
         | Function(Atan, Number n) when n = 1N -> pi/4 
         | Function(Atan, Number n) when n = 0N -> 0Q 
         | Function(Ln, Function(Exp, x)) -> simplifyLoop x
         | Function(f, x) -> Function(f, (simplifyLoop x)) 
         | Sum     [x]  
         | Product [x] -> simplifyLoop x
         | Product l -> Product (List.map simplifyLoop l)
         | Sum l -> Sum (List.map simplifyLoop l)
         | x -> x
      simplifyLoop fx |> Rational.reduce
      
type Expression with
   member t.ToFormattedString() = expressionFormater t 
   member t.ToFloat() = (Evaluate.evaluate standardSymbols t).RealValue
   member t.ToComplex() = (Evaluate.evaluate standardSymbols t).ComplexValue
   member t.ToInt() = match t with Number n -> int n | _ -> failwith "not a number"
   member t.Rational() = match t with Number n -> n | _ -> failwith "not a number"
module Expression =
   let toFloat (x:Expression) = x.ToFloat()

type Complex(r:Expression,i:Expression) =  
  member __.Real = r
  member __.Imaginary = i
  member __.Conjugate = Complex(r, -i)
  member __.Magnitude = sqrt (r**2 + i**2)
  member __.ToComplex() = System.Numerics.Complex(r.ToFloat(), i.ToFloat())
  member __.Phase =
     let x,y = r.ToFloat(), i.ToFloat()
     if  x > 0. then arctan (i/r) 
     elif x < 0. && y >= 0. then Trigonometric.simplify (arctan (i/r) + pi)
     elif x < 0. && y < 0. then Trigonometric.simplify (arctan (i/r) - pi)
     elif x = 0. && y > 0. then pi/2
     elif x = 0. && y < 0. then -pi/2
     else Undefined

  static member Zero = Complex(0Q, 0Q)
  static member (~-) (a:Complex) = Complex(-a.Real, -a.Imaginary)
  member c.Pow(n:Expression, phase) = 
         let r = c.Magnitude
         let angle = c.Phase
         r ** n * Complex(cos (n * (angle + phase)) |> Algebraic.simplify false |> Trigonometric.simplify, 
                          sin (n * (angle + phase)) |> Algebraic.simplify false |> Trigonometric.simplify) 
  static member Pow (c:Complex, n:int) = c ** (Expression.FromInt32 n) 
  static member Pow (c:Complex, n:Expression) = 
              let r = c.Magnitude
              let angle = c.Phase
              r ** n * Complex(cos (n * angle) |> Algebraic.simplify false |> Trigonometric.simplify, sin (n * angle) |> Algebraic.simplify false |> Trigonometric.simplify) 
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

  static member magnitude (c:Complex) = c.Magnitude
  
  new(r) = Complex(r, 0Q)

  override t.ToString() = sprintf "(%s, %s)" (t.Real.ToFormattedString()) (t.Imaginary.ToFormattedString())  



let rec containsVar x = function
   | Identifier _ as sy when sy = x -> true  
   | Power(p, n)  -> containsVar x n || containsVar x p   
   | Function(_,fx) -> containsVar x fx  
   | Product l  
   | Sum     l -> List.exists (containsVar x) l
   | _ -> false


module Vars = 
  let a = symbol "a"
  let b = symbol "b"
  let c = symbol "c"
  let d = symbol "d"
  let e = symbol "e"
  let f = symbol "f"
  let g = symbol "g"
  let h = symbol "h"
  let i = symbol "i"
  let n = symbol "n"
  let r = symbol "r"
  let t = symbol "t"
  let u = symbol "u"
  let v = symbol "v"
  let x = symbol "x"
  let y = symbol "y"
  let z = symbol "z"

  let x0 = symbol "x₀"
  let x1 = symbol "x₁"
  let x2 = symbol "x₂"
  let x3 = symbol "x₃"
  let v0 = symbol "v₀"
  let y1 = symbol "y₁"
  let y2 = symbol "y₂"

  let phi = symbol "φ"   
  let π = pi
  let pi = pi
