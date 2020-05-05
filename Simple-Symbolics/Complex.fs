namespace MathNet.Symbolics

open Core
open Core.Vars
open Utils.Constants
open MathNet.Numerics
open MathNet.Symbolics.NumberTheory

type Complex(r : Expression, i : Expression) =  
    member __.Real = r
    member __.Imaginary = i
    member __.Conjugate = Complex(r, -i)
    member __.Magnitude = sqrt (r ** 2 + i ** 2)
    member __.ToComplex() = 
        match (r, i) with 
        | IsFloatingPoint x, IsFloatingPoint y ->
            Some(System.Numerics.Complex(x, y))
        | _ -> None
    member __.Phase = Trigonometry.simplifyTrigTerm (Operators.arctan2 i r)
    static member Abs(c:Complex) = Complex c.Magnitude
    static member Zero = Complex(0Q, 0Q)
    static member (~-) (a : Complex) = Complex(-a.Real, -a.Imaginary)
    static member magnitude (c:Complex) = c.Magnitude

    static member Pow(c : Complex, n : int) = c ** (Expression.FromInt32 n)

    static member Pow(c : Complex, n : Expression) = 
        let imaginaryPower n = 
            let effectiveN = n % 4
            match effectiveN with 
            | 0 -> Complex(1Q, 0Q)
            | 1 -> Complex(0Q, 1Q)
            | 2 -> Complex(-1Q, 0Q) 
            | 3 -> Complex(0Q, -1Q) 
            | _ -> Complex(1Q, 0Q) 

        if c.Imaginary = 0Q then Complex (c.Real ** n)
        elif c.Real = 0Q && Expression.isInteger n then  
            c.Imaginary ** n * imaginaryPower (Expression.toInt n)
        else
            let r = Expression.Simplify c.Magnitude
            let angle = c.Phase
            r ** n * Complex(cos (n * angle)
                        |> Expression.simplify false 
                        |> Trigonometric.simplify,
                        sin (n * angle)
                        |> Expression.simplify false 
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
        let i, useparens = if Utils.expressionFormat = "Infix" then "ⅈ", ("(", ")") else "i", ("\\left(", "\\right)")
        match t.Real, t.Imaginary with
        | c when c = (0Q, 0Q) -> sprintf "0"
        | r, _ when r = 0Q -> sprintf "%s%s" (t.Imaginary.ToFormattedString()) i
        | _, i when i = 0Q -> sprintf "%s" (t.Real.ToFormattedString()) 
        | _ , Number n when n = 1N ->
            sprintf "%s + %s" (t.Real.ToFormattedString()) i
        | _ , Number _
        | _ , Identifier _ -> 
            sprintf "%s + %s%s" (t.Real.ToFormattedString()) (t.Imaginary.ToFormattedString()) i
        | _ ->
            let lparens, rparens = if t.Imaginary = 0Q then "", "" else useparens
            sprintf "%s + %s%s%s%s" (t.Real.ToFormattedString()) i lparens (t.Imaginary.ToFormattedString()) rparens
    
    override t.GetHashCode () = hash (t.Real, t.Imaginary)

    override x.Equals(b) =
        match b with
        | :? Complex as y -> (x.Real, x.Imaginary) = (y.Real, y.Imaginary)
        | _ -> false

module Complex =  
    open Utils

    let i = Complex(0Q, 1Q)  

    let toExpression (c:Complex) =
        c.Real + (c.Imaginary * Constants.i)

    //powers of i have a simple pattern with a cycle of 4.
    let imaginaryPowerExpression n = 
        let effectiveN = n % 4
        match effectiveN with 
        | 0 -> 1Q
        | 1 -> Constants.i
        | 2 -> -1Q
        | 3 -> -Constants.i
        | _ -> 1Q
    
    //Complex numbers are multiplied with FOIL. Expand it, replace i^2 with -1 and simplify.   
    let simplifyExpression x =
        x
        |> recmap (function  
            | SquareRoot(IsRealNumber (IsNegativeNumber e)) -> Constants.i * sqrt(-e) //negative square roots are imaginary.
            | Power(IsRealNumber  (IsNegativeNumber e), Number n) when n.Denominator = 2I -> 
                (Constants.i * sqrt(-e)) ** Operators.fromInteger n.Numerator 
            | x -> x )
        |> Algebraic.expand
        |> recmap (function
               | (Power(Constant Constant.I, Number n)) ->
                    imaginaryPowerExpression (int n)        
               | x -> x)
        |> Expression.FullSimplify
        |> Algebraic.groupInSumWith Constants.i

    let ofExpression zx =
        Structure.partition (Expression.containsExpression Constants.i) zx
        |> function
        | (Some b, a) -> Complex(a, b / Constants.i)
        | (_, a) -> Complex(a, 0Q)
