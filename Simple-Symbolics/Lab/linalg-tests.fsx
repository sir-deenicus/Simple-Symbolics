#load "linear-algebra.fsx"
open MathNet.Symbolics
open Core.Vars
open ``Linear-algebra``
open Core
open Core.Units

dot [a ; b] [cos a;b] |> Infix.format //|> Evaluate.evaluate symbols2
 
vecmatrixmult [a; b] [[a;b];[c;d]] |> List.map Infix.format 
 
let vec = Vector [1Q; 2Q; 3Q]
let m = Matrix([[1Q;2Q;3Q]; [3Q;4Q;5Q] ])

2Q * vec * m
m * vec
m * 2Q

let m2 = MathNet.Numerics.LinearAlgebra.DenseMatrix.ofRowList [[1.;2.;3.]; [3.;4.;5.]]
let v2 = MathNet.Numerics.LinearAlgebra.DenseVector.ofList [1.; 2.;3.]

2. * v2 * m2
m2 * v2

m2 * 2.

vec * vec
v2 * v2  

let vr = Vector([1 * meter; 2 * meter])
let vf = Vector ([3 * N; a * N])
 
vf + 3Q * vf

Units.simplifyUnits (vr * vf)
Units.To(vr * vf, J)
 