#load "core.fsx"

open MathNet.Symbolics
open Core.Vars
open Core

 
let sq = sqrt 2Q / 2

sq.ToFloat()

let a1 = Complex(-2Q, sqrt 5Q)
-a1

let b1 = Complex(3Q, 2Q)

let ca = Complex(3Q, 3Q)

 
(ca ** (5Q/1))//.ToComplex()
 
let za = System.Numerics.Complex(-2.,System.Math.Sqrt 5.)
let zb = System.Numerics.Complex(3.,2.)
zb ** 3.5
za.Phase
a1.Phase.ToFormattedString()
a1.Phase.ToFloat()
-za
a1*b1
za * zb
a1 + b1
za + zb
za - zb
a1 - b1
za ** (1./3.)
za ** 2.
za * za
5. * za
5Q * a1

Complex(5Q, 7Q) * -5Q  
Complex(5Q, 7Q) * Complex -5Q  


System.Numerics.Complex(5.,7.) * System.Numerics.Complex(-5.,0.)

List.sum [Complex 5Q ; Complex 3Q]

Complex(a, b) * Complex(c, 0Q)
Complex(a, b) * c
a1 * a1.Conjugate
a1.Magnitude.ToFormattedString()
a1.Magnitude.ToFloat()
za.Magnitude

MathNet.Numerics.Complex.conjugate za
za * MathNet.Numerics.Complex.conjugate za
a1.Conjugate 

Infix.format sq

Polynomial.factorSquareFree x (x ** 3 + 2 * x) |> Infix.format

Polynomial.variables (x**3 + 2 * x)

Algebraic.expand ((x+1) **4 / (4)) |> Infix.format

Polynomial.factorSquareFree b (a ** 2 + 2 * a * b + b ** 2) |>  (Infix.format)

open Units

Units.ToUnit(btu / ft ** 3, mega * J / meter ** 3).Value.Evaluate()
(btu / ft ** 3).Evaluate(false)
 
Units.To (1 * tera * flops, giga * flops)
Units.To(5 * mega * bytes, mega * bytes)

5 * kilo * W * hr
Units.To (0.01 * kilo * W , W)

Units.To (List.fold (+) (0Q * hr) [5Q * hr; 2Q * hr], hr)
Units.To (List.sum  [5Q * hr; 2Q * hr], hr)
5Q * kg ** 2 / meter  + 5Q * kg * 2Q * kg / (3Q * meter)

1Q / (10Q*kg) 

Units.To (5Q * km, km )
Units.simplifyUnits (5 * kilo * meter)
Units.simplifyUnits(List.sum  [5Q * hr; 2Q * hr])
5Q * meter + 5Q * km

Units.To (10 * kilo * W * hr, kilo * W * hr)
Units.To (10 * kilo * W * hr, J )
Units.simplifyUnits (kilo * W * hr)
Units.simplifyUnits (J / sec)
Units.To (5 * meter / sec, km/ hr) 
Units.To(kilo * W / meter ** 2, W / meter ** 2)

let pn = 1/2Q * (a * meter / sec ** 2) * (t * sec) **2 

Units.differentiate (t * sec) pn |> Units.differentiate (t * sec)

