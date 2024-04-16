namespace MathNet.Symbolics

open MathNet.Symbolics

open Core
open Core.Vars
open Utils.Constants
open MathNet.Numerics
open MathNet.Symbolics.NumberProperties
open Prelude.Common

type Quaternion(a: Expression, b: Expression, c: Expression, d: Expression) =
    new(a: Expression) = Quaternion(a, 0Q, 0Q, 0Q)

    new(a: Expression, v: Expression list) =
        match v with
        | b :: c :: d :: _ -> Quaternion(a, b, c, d)
        | b :: c :: [] -> Quaternion(a, b, c, 0Q)
        | b :: [] -> Quaternion(a, b, 0Q, 0Q)
        | [] -> Quaternion(a, 0Q, 0Q, 0Q)

    member this.a = a
    member this.b = b
    member this.c = c
    member this.d = d

    member this.Norm = sqrt (a ** 2 + b ** 2 + c ** 2 + d ** 2)

    member this.Conjugate = Quaternion(a, -b, -c, -d)

    member this.Inverse = this.Conjugate / (this.Norm ** 2)

    member this.Unit = this / this.Norm

    member this.RealPart = a

    member this.ImaginaryPart = Quaternion(0Q, b, c, d)

    member this.Scalar = a

    member this.Vector = Quaternion(0Q, b, c, d) 

    member this.PolarFormParts =
        let theta = Operators.arccos (a / this.Norm)
        theta, cos theta + this.ImaginaryPart.Unit * sin theta

    member __.ToNumericsQuaternion() =
        match (a, b, c, d) with
        | AsFloatingPoint a, AsFloatingPoint b, AsFloatingPoint c, AsFloatingPoint d ->
            Some(System.Numerics.Quaternion(float32 a, float32 b, float32 c, float32 d))
        | _ -> None

    member __.ToReal() =
        if b = 0Q && c = 0Q && d = 0Q then Some a else None

    member __.ToComplex() =
        if b = 0Q && c = 0Q && d = 0Q then Some(Complex(a, 0Q))
        elif c = 0Q && d = 0Q then Some(Complex(a, b))
        else None

    static member i = Quaternion(0Q, 1Q, 0Q, 0Q)

    static member j = Quaternion(0Q, 0Q, 1Q, 0Q)

    static member k = Quaternion(0Q, 0Q, 0Q, 1Q)

    static member (+)(q1: Quaternion, q2: Quaternion) =
        Quaternion(q1.a + q2.a, q1.b + q2.b, q1.c + q2.c, q1.d + q2.d)

    static member (+)(q: Quaternion, s: Expression) = Quaternion(q.a + s, q.b, q.c, q.d)

    static member (+)(s: Expression, q: Quaternion) = Quaternion(q.a + s, q.b, q.c, q.d)

    static member (-)(q1: Quaternion, q2: Quaternion) =
        Quaternion(q1.a - q2.a, q1.b - q2.b, q1.c - q2.c, q1.d - q2.d)

    static member (*)(q1: Quaternion, q2: Quaternion) =
        let a = q1.a * q2.a - q1.b * q2.b - q1.c * q2.c - q1.d * q2.d
        let b = q1.a * q2.b + q1.b * q2.a + q1.c * q2.d - q1.d * q2.c
        let c = q1.a * q2.c - q1.b * q2.d + q1.c * q2.a + q1.d * q2.b
        let d = q1.a * q2.d + q1.b * q2.c - q1.c * q2.b + q1.d * q2.a
        Quaternion(a, b, c, d)

    static member (*)(q: Quaternion, s: Expression) =
        Quaternion(q.a * s, q.b * s, q.c * s, q.d * s)

    static member (*)(s: Expression, q: Quaternion) =
        Quaternion(q.a * s, q.b * s, q.c * s, q.d * s)

    static member (/)(q: Quaternion, s: Expression) =
        Quaternion(q.a / s, q.b / s, q.c / s, q.d / s)

    static member (/)(q1: Quaternion, q2: Quaternion) = q1 * q2.Inverse

    static member (~-)(q: Quaternion) = Quaternion(-q.a, -q.b, -q.c, -q.d)

    static member Pow(q: Quaternion, n: int) =
        //if we have f a b = a * b then we can use repeat as follows:
        repeat n ((*) q) Quaternion.One

    static member Pow(q: Quaternion, n: Expression) =
        let theta, qvec = q.PolarFormParts

        q.Norm ** n
        * (Trigonometric.fullsimplify (cos (n * theta))
           + qvec * Trigonometric.fullsimplify (sin (n * theta)))

    static member Zero = Quaternion(0Q, 0Q, 0Q, 0Q)

    static member One = Quaternion(1Q, 0Q, 0Q, 0Q)


module Quaternion = 
    let dotProduct (q1: Quaternion) (q2: Quaternion) =
        if q1.a = 0Q && q2.a = 0Q then
            -(q1 * q2).Scalar
        else failwith "Dot product is only defined for pure quaternions"

    let crossProduct (q1: Quaternion) (q2: Quaternion) =
        if q1.a = 0Q && q2.a = 0Q then
            (q1 * q2).Vector
        else failwith "Cross product is only defined for pure quaternions"