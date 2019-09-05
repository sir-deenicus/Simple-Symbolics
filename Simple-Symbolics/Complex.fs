namespace MathNet.Symbolics

open Core
open Core.Vars
open Core.Constants

type Complex(r : Expression, i : Expression) =
    member __.Real = r
    member __.Imaginary = i
    member __.Conjugate = Complex(r, -i)
    member __.Magnitude = sqrt (r ** 2 + i ** 2)
    member __.ToComplex() = System.Numerics.Complex(r.ToFloat(), i.ToFloat())

    member __.Phase =
        let x, y = r.ToFloat(), i.ToFloat()
        if x > 0. then arctan (i / r)
        elif x < 0. && y >= 0. then Trigonometric.simplify (arctan (i / r) + pi)
        elif x < 0. && y < 0. then Trigonometric.simplify (arctan (i / r) - pi)
        elif x = 0. && y > 0. then pi / 2
        elif x = 0. && y < 0. then -pi / 2
        else Undefined

    static member Zero = Complex(0Q, 0Q)
    static member (~-) (a : Complex) = Complex(-a.Real, -a.Imaginary)
    static member magnitude (c:Complex) = c.Magnitude
    member c.Pow(n : Expression, phase) =
        let r = c.Magnitude
        let angle = c.Phase
        r ** n * Complex(cos (n * (angle + phase))
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify,
                         sin (n * (angle + phase))
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify)

    static member Pow(c : Complex, n : int) = c ** (Expression.FromInt32 n)

    static member Pow(c : Complex, n : Expression) =
        let r = c.Magnitude
        let angle = c.Phase
        r ** n * Complex(cos (n * angle)
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify,
                         sin (n * angle)
                         |> Algebraic.simplify false
                         |> Trigonometric.simplify)

    static member (+) (a : Complex, b : Expression) =
        Complex(a.Real + b, a.Imaginary)
    static member (+) (a : Expression, b : Complex) =
        Complex(a + b.Real, b.Imaginary)
    static member (+) (a : Complex, b : Complex) =
        Complex(a.Real + b.Real, a.Imaginary + b.Imaginary) 
    static member (-) (a : Complex, b : Expression) =
        Complex(a.Real - b, a.Imaginary)
    static member (-) (a : Expression, b : Complex) =
        Complex(a - b.Real, b.Imaginary)
    static member (-) (a : Complex, b : Complex) =
        Complex(a.Real - b.Real, a.Imaginary - b.Imaginary)
    static member (*) (a : Complex, b : Complex) =
        Complex
            (a.Real * b.Real - a.Imaginary * b.Imaginary,
             a.Imaginary * b.Real + a.Real * b.Imaginary)
    static member (*) (a : Complex, b : Expression) =
        Complex(a.Real * b, a.Imaginary * b)
    static member (*) (a : Expression, b : Complex) =
        Complex(a * b.Real, a * b.Imaginary)
    static member (/) (a : Complex, b : Expression) =
        Complex(a.Real / b, a.Imaginary / b)

    static member (/) (a : Complex, b : Complex) =
        let conj = b.Conjugate
        (a * conj) / (b * conj).Real

    static member (/) (a : Expression, b : Complex) = (Complex a) / b
    member c.Simplify() = Complex(Expression.FullerSimplify r, Expression.FullerSimplify i)
    new(r) = Complex(r, 0Q)
    override t.ToString() =
            match t.Real, t.Imaginary with
              | c when c = (0Q, 0Q) -> sprintf "0"
              | r, _ when r = 0Q -> sprintf "%sⅈ" (t.Imaginary.ToFormattedString())
              | _ ->
                sprintf "%s + ⅈ%s" (t.Real.ToFormattedString()) (t.Imaginary.ToFormattedString())

module Complex = 
    let i = Complex(0Q, 1Q) 