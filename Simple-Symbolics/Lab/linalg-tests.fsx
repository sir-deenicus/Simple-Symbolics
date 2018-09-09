#load "linear-algebra.fsx"
open MathNet.Symbolics
open Core.Vars
open ``Linear-algebra``

dot [a ; b] [cos a;b] |> Infix.format //|> Evaluate.evaluate symbols2
 
vecmatrixmult [a; b] [[a;b];[c;d]] |> List.map Infix.format 
 
let v = Vector [1Q; 2Q; 3Q]
let m = Matrix([[1Q;2Q;3Q]; [3Q;4Q;5Q] ])

2Q * v * m
m * v
m * 2Q

let m2 = MathNet.Numerics.LinearAlgebra.DenseMatrix.ofRowList [[1.;2.;3.]; [3.;4.;5.]]
let v2 = MathNet.Numerics.LinearAlgebra.DenseVector.ofList [1.; 2.;3.]

2. * v2 * m2
m2 * v2

m2 * 2.