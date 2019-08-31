#load "core.fsx"

open MathNet.Symbolics
open Core.Vars
open Core
open System 

Structure.recursiveFilter (
        function 
        | Identifier(Symbol s) when String.forall Char.IsUpper s -> true
        | Number _ -> true 
        | _ -> false) (f+3Q)

let a1 = Complex(-2Q,sqrt 5Q)

-a1

let b1 = Complex(3Q,2Q)
let ca = Complex(3Q,3Q)

(ca ** (5Q / 1)) //.ToComplex()

let numericComplexA = System.Numerics.Complex(-2.,System.Math.Sqrt 5.)
let numbericComplexB = System.Numerics.Complex(3.,2.)

numbericComplexB ** 3.5
numericComplexA.Phase
a1.Phase.ToFormattedString()
a1.Phase.ToFloat()
-numericComplexA
a1 * b1
numericComplexA * numbericComplexB
a1 + b1
numericComplexA + numbericComplexB
numericComplexA - numbericComplexB
a1 - b1
numericComplexA ** (1. / 3.)
numericComplexA ** 2.
numericComplexA * numericComplexA
5. * numericComplexA
5Q * a1
Complex(5Q,7Q) * -5Q
Complex(5Q,7Q) * Complex -5Q
System.Numerics.Complex(5.,7.) * System.Numerics.Complex(-5.,0.)
List.sum [Complex 5Q
          Complex 3Q]
Complex(a,b) * Complex(c,0Q)
Complex(a,b) * c
a1 * a1.Conjugate
a1.Magnitude.ToFormattedString()
a1.Magnitude.ToFloat()
numericComplexA.Magnitude
MathNet.Numerics.Complex.conjugate numericComplexA
numericComplexA * MathNet.Numerics.Complex.conjugate numericComplexA
a1.Conjugate
Polynomial.factorSquareFree x (x ** 3 + 2 * x) |> Infix.format
Polynomial.variables(x ** 3 + 2 * x)
Algebraic.expand((x + 1) ** 4 / (4)) |> Infix.format
Polynomial.factorSquareFree b (a ** 2 + 2 * a * b + b ** 2) |> (Infix.format)

open Units

Units.ToUnit(btu / ft ** 3,mega * J / meter ** 3).Value.Evaluate()
(btu / ft ** 3).Evaluate(false)
Units.To(1 * tera * flops,giga * flops)
Units.To(5 * mega * bytes,mega * bytes)
5 * kilo * W * hr
Units.To(0.01 * kilo * W,W)
Units.To(List.fold (+) (0Q * hr) [5Q * hr
                                  2Q * hr],hr)
Units.To(List.sum [5Q * hr
                   2Q * hr],hr)
5Q * kg ** 2 / meter + 5Q * kg * 2Q * kg / (3Q * meter)
1Q / (10Q * kg)
Units.To(5Q * km,km)
Units.simplifyUnits(5 * kilo * meter)
Units.simplifyUnits(List.sum [5Q * hr
                              2Q * hr])
5Q * meter + 5Q * km
Units.To(10 * kilo * W * hr,kilo * W * hr)
Units.To(10 * kilo * W * hr,J)
Units.simplifyUnits(kilo * W * hr)
Units.simplifyUnits(J / sec)
Units.To(5 * meter / sec,km / hr)
Units.To(kilo * W / meter ** 2,W / meter ** 2)

let pn = 1 / 2Q * (a * meter / sec ** 2) * (t * sec) ** 2

Units.differentiate (t * sec) pn |> Units.differentiate(t * sec)
///////////
BigRational.fromFloat(1e-26)
 

[2. ** 3.
 2. ** 5.
 2. ** 4.
 5. ** 4.
 168.
 144.
 4.
 1048.
 25.
 100.
 64.
 1234212.
 -16.
 -32.
 -64.
 -145.]
|> List.map(BigRational.fromFloat >> Expression.FromRational)
|> List.map(fun x -> 
       x.ToFormattedString(),
       let y = Algebraic.simplifySquareRoot (sqrt x)
       y |> Option.map Expression.toFormattedString) //, y.ToFloat() ** 2.)
Algebraic.simplifySquareRoot (sqrt -145Q)
(primeFactorsExpr 5324Q).ToFormattedString()
Core.expressionFormater <- Infix.format
Logarithm.powerRule(ln(x ** 2))

sqrt 20Q |> Algebraic.simplifySquareRoot

let vr = sqrt 32Q |> Algebraic.simplifySquareRoot |> Option.get  


[ 
    Algebraic.consolidateSums2 (a * (1/3Q) * b * c - e * b * c) 
    Algebraic.consolidateSums2 (a * 3Q * b * c - e * b * c) 
    Algebraic.consolidateSums2 (a * 3Q * b * c + 15Q * e * b * c)
    Algebraic.consolidateSums2 (a * (1/3Q) * b * c - e * b * c * (1/3Q) ) 
    Algebraic.consolidateSums2 (a * (1/3Q) * b * c +  e * b * c * (1/3Q) ) 
    Algebraic.consolidateSums2 (a * (1/3Q) * b +  e * b * (1/3Q) ) 
    Algebraic.consolidateSums2 (a * (3Q) * b +  e * b * (3Q) ) 
    Algebraic.consolidateSums2 (a * 3Q * b * c - 3Q * e * f * g)
    Algebraic.consolidateSums2 (a * 3Q * b * c + 3Q * e * f * g) 
    Algebraic.consolidateSums2 (a * 1/3Q * b * c + 1/3Q * e * f * g)  
    Algebraic.consolidateSums2 (a * 3Q * b * c - 15Q * e * f * g) 
] 

Algebraic.intersectAll [a * b * c * (a + b); a + b]
Algebraic.intersectAll [a * b * c + (a + b); a + b]