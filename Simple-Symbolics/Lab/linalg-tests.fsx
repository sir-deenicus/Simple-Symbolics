﻿#r @"../bin/Debug/net47/MathNet.Numerics.dll"
#r @"../bin/Debug/net47/MathNet.Numerics.FSharp.dll"
#r @"../bin/Debug/net47/MathNet.Symbolic.Ext.dll"
#r @"../bin/Debug/net47/Simple-Symbolics.dll"

open MathNet.Symbolics
open Core.Vars
open Core
open Units
open MathNet.Symbolics.LinearAlgebra

dot [a ; b] [cos a;b]  
 
vecmatrixmult [a; b] [[a;b];[c;d]]  
 
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
 
let vu = Vector([ 400 * W; 45 * tera * flops; 16 * giga * bytes])

16Q * vu |> Vector.map Units.simplifyUnits

30Q * 16Q * vu.[0] |> Units.simplifyUnits
30Q * 16Q * vu.[0] * 14Q * days |> Units.simplifyUnits
Units.To(30Q * 16Q * vu.[0] * 14Q * days, mega * W * hr) 
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

Complex(1/4Q,3Q) * Vector ([Complex 1Q; Complex (2Q, 1Q)])


Matrix.inverse (Matrix mu) * (Matrix mu)

let rpm2 = Matrix [[1Q;0Q;-1Q];[1Q;0Q;0Q];[1Q;-1Q;0Q];[0Q;-1Q;1Q];[-1Q;0Q;1Q]]
rpm2.[*, 1] = Vector [0Q;0Q;-1Q;-1Q;0Q]

rpm2.[0, *] = Vector [1Q;0Q;-1Q]


rpm2.[1..3,1..2].AsList = [[0Q;0Q];[-1Q;0Q];[-1Q;1Q]]
