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

let matr = MathNet.Numerics.LinearAlgebra.DenseMatrix.ofRowList [[1.;2.;3.]; [3.;4.;5.]]
let v2 = MathNet.Numerics.LinearAlgebra.DenseVector.ofList [1.; 2.;3.]

2. * v2 * matr
matr * v2

matr * 2.

vec * vec
v2 * v2  

let vr = Vector([1 * meter; 2 * meter])
let vf = Vector ([3 * N; a * N])
 
vf + 3Q * vf

Units.simplifyUnits (vr * vf)
Units.To(vr * vf, J)
 

///////////////
let mu = [[Complex 1Q; Complex (2Q, 1Q)];[Complex (1/2Q,3Q);Complex 4Q]]
let mi = [[ 1Q;  2Q];[ 3Q; 4Q]]
let m2 = [[a;b];[c;d]] 
let m2n = [[4;7];[2;6]] |> List.map (List.map Expression.FromInt32)
let m3 = [[a;b;c];[d;e;f];[g;h;i]]  
let m3n = [[-3;2;-5]; [-1;0;-2];[3;-4;1]] |> List.map (List.map Expression.FromInt32)
let m4 = [[a;b;c;a];[d;e;f;d];[g;h;i;g];[a;b;c;d]]


Matrix.identity 3  
// x^4 + 2x + x^2 = 0, x(x^3 + 2 + x) = 0
adjugate m2 |> List.map (List.map Infix.format)   

Matrix.inverse (Matrix m3) //|> List.map (List.map Infix.format) 

Matrix.inverse (Matrix m2) * (Matrix m2) |> Matrix.map (Rational.simplify x)

adjugate m3n |> List.map (List.map Infix.format) 
 
Matrix m3n |> Matrix.determinant

Matrix (mu) |> Matrix.determinant

Matrix.inverse (Matrix mu) * (Matrix mu)