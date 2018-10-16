
#I @"C:\Users\Admin\Documents\Visual Studio 2017\Libs\MathNet"
#r @".\lib\net461\MathNet.Numerics.dll"
#r @".\lib\net45\MathNet.Numerics.FSharp.dll"
#r @"..\fparsec\net40-client\fparsecCs.dll"
#r @"..\fparsec\net40-client\fparsec.dll"
#r @".\symbolics\net40\mathnet.symbolics.dll"

open MathNet.Symbolics 
open MathNet.Numerics
open System

let flip f a b = f b a

let pairmap f (x,y) = f x , f y

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
 
type Expression with
   member t.ToFormattedString() = expressionFormater t 
   member t.ToFloat() = (Evaluate.evaluate standardSymbols t).RealValue
   member t.ToComplex() = (Evaluate.evaluate standardSymbols t).ComplexValue
   member t.ToInt() = match t with Number n -> int n | _ -> failwith "not a number"
   member t.Rational() = match t with Number n -> n | _ -> failwith "not a number"
module Expression =
   let toFloat (x:Expression) = x.ToFloat()

let inline factors toint f x = 
    let x' = toint x 
    let sqrtx = int(sqrt (float x'))
    [for n in 1..sqrtx do 
       let m = x' / n
       if x' % n = 0 then yield f n; if m <> n then yield f m]
    |> List.sortByDescending toint

let factorsExpr = factors (fun (i:Expression) -> i.ToInt()) (Expression.FromInt32)

let inline primefactors factor x =
    let rec loop x =
        match factor x with
        | [one] -> [one]
        | [x; _] -> [x]
        | _::(tf::_) -> 
            let r = x / tf
            let f1, f2 = loop r, loop tf
            f1 @ f2
        | _ -> failwith "unexpected error"
    loop x    

let groupPowers pl =
       List.groupBy id pl 
    |> List.map (fun (x, l) -> 
        if l.Length = 1 then x         
        else Power(x , Expression.FromInt32 (List.length l)) )  

let primeFactorsExpr = primefactors factorsExpr >> groupPowers >> Product

let simplifySquareRoot (num:Expression) =
    let n = abs num
    let sqRootGrouping = 
        function 
        | (Power(x, Number n)) when n > 1N -> 
            if (int n % 2 = 0) then x ** (Expression.FromRational (n/2N)), 1Q
            elif n = 3N then x, x
            else x, Power(x, Number (n - 2N)) 
        | x -> 1Q, x  

    let outr, inr =        
        primefactors factorsExpr n 
        |> groupPowers
        |> List.map sqRootGrouping 
        |> List.unzip

    
    let isneg = num.ToInt() < 0
    List.fold (*) 1Q outr * sqrt(List.fold (*) (if isneg then -1Q else 1Q) inr)

open Operators 
 
module Algebraic = 
  let simplify simplifysqrt fx =
      let rec simplifyLoop = function               
         | Power (x, Number n) when n = 1N -> simplifyLoop x
         | Power (Number x, _) when x = 1N -> 1Q  
         | Power (Product[x], n) 
         | Power (Sum[x], n) -> simplifyLoop (Power(x, n))
         | Power (Power (x, a), b) -> simplifyLoop(Power(x, (a * b)))
         | Power (Number _ as x,n) when n = 1Q/2Q && simplifysqrt -> simplifySquareRoot x
         | Power (x,n) -> Power(simplifyLoop x, simplifyLoop n) 
         | Function(Atan, Number n) when n = 1N -> pi/4 
         | Function(Atan, Number n) when n = 0N -> 0Q 
         | Function(f, x) -> Function(f, (simplifyLoop x)) 
         | Sum     [x]  
         | Product [x] -> simplifyLoop x
         | Product l -> Product (List.map simplifyLoop l)
         | Sum l -> Sum (List.map simplifyLoop l)
         | x -> x
      simplifyLoop fx
      
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
  new(r) = Complex(r, 0Q)
  override t.ToString() = sprintf "(%s, %s)" (t.Real.ToFormattedString()) (t.Imaginary.ToFormattedString())  


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
  member t.Evaluate (m,?usealt) = Evaluate.evaluate m q, match usealt with Some false -> u.ToFormattedString() | _ -> t.AltUnit 
  member t.Evaluate ?usealt = q.ToFloat(), match usealt with Some false -> u.ToFormattedString() | _ -> t.AltUnit 
  member __.ToAltString() = sprintf "%s %s" (u.ToFormattedString()) altunit
  static member Zero = Units(0Q, 0Q)
  static member (+) (a:Units,b:Units) = 
    if a.Unit = b.Unit then
      Units(a.Quantity + b.Quantity, a.Unit, a.AltUnit)    
    elif b.Unit = 0Q then Units(a.Quantity, a.Unit, a.AltUnit)
    elif a.Unit = 0Q then Units(b.Quantity, b.Unit, b.AltUnit)
    else failwith "Units don't match"
  static member (~-) (a:Units) = (-a.Quantity, a.Unit, a.AltUnit) 
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
    Units(Algebraic.simplify true (a.Quantity ** b), Algebraic.simplify true (a.Unit ** b))  
  static member (/) (a:Units, b:Expression) = Units( a.Quantity / b, a.Unit, a.AltUnit)
  static member (/) (a:Units, b:Units) = Units(a.Quantity / b.Quantity, a.Unit / b.Unit, a.AltUnit + "/" + b.AltUnit)
  static member (/) (a:Expression, b:Units) = Units(a / b.Quantity, 1 / b.Unit, b.AltUnit + "^-1") 
  static member ToUnit (a:Units, b:Units) = 
      if a.Unit = b.Unit then 
         let altunit = if b.AltUnit = "" then 
                         Units.numstr b.Quantity + " " + b.Unit.ToFormattedString() 
                       else b.AltUnit
         Some ( Units((a / b).Quantity,b.Unit, altunit) ) 
      else None 
  static member To (a:Units, b:Units) = 
      if a.Unit = b.Unit then 
         let altunit = if b.AltUnit = "" then 
                         Units.numstr b.Quantity + " " + b.Unit.ToFormattedString() 
                       else b.AltUnit
         Some (sprintf "%s %s" ((a / b).Quantity.ToFormattedString()) altunit ) 
      else None 
  static member To (a:Units, b:Units,unitstr) = if a.Unit = b.Unit then Some (sprintf "%s %s" ((a / b).Quantity.ToFormattedString()) unitstr ) else None 

  override t.ToString() = sprintf "(%s, %s)" (t.Quantity.ToFormattedString()) (t.Unit.ToFormattedString())  
  

module Units =
  let (^) a b = Units(a,b)
  let setAlt alt (u:Units) = u.AltUnit <- alt; u   

  let kg = Units(1Q, Operators.symbol "kg", "kg")
  let meter = Units(1Q, Operators.symbol "meters", "meter")
  let sec = Units(1Q, Operators.symbol "sec", "sec")

  let flops = Units(1Q, Operators.symbol "flops")
  let bits = Units(1Q, Operators.symbol "bits")
  let bytes = 8Q * bits |> setAlt "bytes"
   
  let N = kg * meter / sec ** 2       |> setAlt "N" 
  let J = kg * meter ** 2 * sec ** -2 |> setAlt "J"   
  let km = 1000Q * meter
  let ft = Expression.FromRational (BigRational.fromFloat 0.3048) * meter
  let btu = Expression.FromRational (BigRational.fromFloat 1055.06) * J
  let W = J / sec |> setAlt "W"
  let kilo = 1000Q
  let mega = 1_000_000Q
  let giga = 1_000_000_000Q
  let tera = 1_000_000_000_000Q
  let minute = 60Q * sec |> setAlt "minute"
  let hr = 60Q * minute  |> setAlt "hr"

  let days = 24Q * hr  |> setAlt "days" 
   
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
   | Power(Sum     l, _)  -> List.exists (containsVar x) l
   | Power(Product l, _)  -> List.exists (containsVar x) l  
   | Power(Function(_, (Identifier (Symbol _) as sy)), _) when sy = x -> true   
   |       Function(_, (Identifier (Symbol _) as sy))     when sy = x -> true
   | Product l -> List.exists (containsVar x) l
   | Sum     l -> List.exists (containsVar x) l
   | _ -> false

let rec replaceSymbol r x = function
   | Identifier _ as sy when sy = x -> r
   | Power(Identifier (Symbol _) as sy, n) when sy = x -> Power(r, n)   
   | Power(Sum l, n)      -> Power(Sum     (List.map (replaceSymbol r x) l), n)
   | Power(Product l, n)  -> Power(Product (List.map (replaceSymbol r x) l), n)
   | Power(Function(f, (Identifier (Symbol _) as sy)), n) when sy = x -> Power(Function(f, r), n)
   |       Function(f, (Identifier (Symbol _ ) as sy))    when sy = x -> Function(f, r)
   | Product l -> Product (List.map (replaceSymbol r x) l)
   | Sum     l -> Sum     (List.map (replaceSymbol r x) l)
   | x -> x

let rec size = function
   | Identifier _ -> 1
   | Power(x, n) -> size x + 1 + size n 
   | Product l -> List.sumBy size l 
   | Sum     l -> List.sumBy size l
   | Function (_, x) -> size x + 1  
   | Approximation _
   | Number _ -> 1 
   | _ -> failwith "unimplemented compute size"
   
let replaceInProductWithShrinkHeuristic replacement test (e:Expression) = 
     let e' = e / test
     if size e' < size e then e' * replacement else e

let replaceProductInSumWithShrinkHeuristic replacement test (e:Expression) = 
     Algebraic.summands e |> List.map (replaceInProductWithShrinkHeuristic replacement test) |> Sum

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
