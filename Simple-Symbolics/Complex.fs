namespace MathNet.Symbolics

open MathNet.Symbolics

open Core
open Core.Vars
open Utils.Constants
open System.Numerics
open MathNet.Numerics
open MathNet.Symbolics.NumberProperties

/// <summary>
/// Represents a complex number.
/// </summary>
/// <param name="r">The real part of the complex number.</param>
/// <param name="i">The imaginary part of the complex number.</param>
type Complex(r: Expression, i: Expression) =
    /// <summary>
    /// Gets the real part of the complex number.
    /// </summary>
    member __.Real = r

    /// <summary>
    /// Gets the imaginary part of the complex number.
    /// </summary>
    member __.Imaginary = i

    /// <summary>
    /// Gets the complex conjugate of the complex number.
    /// </summary>
    member __.Conjugate = Complex(r, -i)

    /// <summary>
    /// Gets the magnitude of the complex number.
    /// </summary>
    member __.Magnitude = Expression.simplify (sqrt (r ** 2 + i ** 2))

    /// <summary>
    /// Converts the complex number to a System.Numerics.Complex value.
    /// </summary>
    member __.ToNumericsComplex() =
        match (r, i) with
        | AsFloatingPoint x, AsFloatingPoint y -> Some(System.Numerics.Complex(x, y))
        | _ -> None

    member __.ToReal() = if i = 0Q then Some r else None

    /// <summary>
    /// Gets the phase of the complex number.
    /// </summary>
    member __.Phase = Trigonometry.simplifyWithTable (Operators.arctan2 i r)

    member __.PolarFormParts =
        let r = __.Magnitude
        let theta = __.Phase

        (r * (Operators.cos theta |> Trigonometric.fullsimplify),

         r * Operators.sin theta |> Trigonometric.fullsimplify)

    member __.ToEulerFormExpression() =
        let r = __.Magnitude
        let theta = __.Phase
        r * Operators.exp (theta * Constant Constant.I)

    member __.ToTrigFormExpression() =
        let r = __.Magnitude
        let theta = __.Phase
        r * Operators.cos theta + r * Constant Constant.I * Operators.sin theta

    static member IsNaN (value: Complex): bool = value.Real.IsNaN || value.Imaginary.IsNaN

    static member IsInfinity (value: Complex): bool =
            Operators.isInfinity value.Real || Operators.isInfinity value.Imaginary
    
    static member IsZero (value: Complex): bool = value = Complex.Zero
     
    /// <summary>
    /// Gets the absolute value of the complex number.
    /// </summary>
    static member Abs(c: Complex) = Complex c.Magnitude

    /// <summary>
    /// Gets the zero complex number.
    /// </summary>
    static member Zero = Complex(0Q, 0Q)
     
    static member One = Complex(1Q, 0Q)

    /// <summary>
    /// Negates the complex number.
    /// </summary>
    static member (~-)(a: Complex) = Complex(-a.Real, -a.Imaginary)

    /// <summary>
    /// Gets the magnitude of the complex number.
    /// </summary>
    static member magnitude(c: Complex) = c.Magnitude

    /// <summary>
    /// Returns the natural logarithm of the complex number.
    /// </summary>
    /// <param name="c">The complex number to take the logarithm of.</param>
    /// <returns>The natural logarithm of the complex number.</returns>
    static member Log(c: Complex) =
        Complex(ln c.Magnitude, c.Phase + 2 * pi * n)

    /// <summary>
    /// Raises the complex number to the specified integer power.
    /// </summary>
    /// <param name="c">The complex number to raise to a power.</param>
    /// <param name="n">The integer power to raise the complex number to.</param>
    /// <returns>The complex number raised to the specified integer power.</returns>
    static member Pow(c: Complex, n: int) = c ** (Expression.FromInt32 n)

    static member Sqrt(c: Complex) = c ** (1Q / 2Q)

    /// <summary>
    /// Raises the complex number to the specified expression power.
    /// </summary>
    /// <param name="c">The complex number to raise to a power.</param>
    /// <param name="n">The expression power to raise the complex number to.</param>
    /// <returns>The complex number raised to the specified expression power.</returns>
    static member Pow(c: Complex, n: Expression) =
        let imaginaryPower n =
            let effectiveN = n % 4

            match effectiveN with
            | 0 -> Complex(1Q, 0Q)
            | 1 -> Complex(0Q, 1Q)
            | 2 -> Complex(-1Q, 0Q)
            | 3 -> Complex(0Q, -1Q)
            | _ -> Complex(1Q, 0Q)

        if
            c.Imaginary = 0Q
            && (Expression.isInteger n
                || Expression.isCertainlyEven (Rational.numerator n)
                || Expression.isPositive c.Real = Some true)
        then
            Complex(c.Real ** n)
        elif
            c.Real = 0Q && Expression.isInteger n
           // || Expression.isCertainlyEven (Rational.numerator n)
        then
            //if Expression.isRationalNumber n then
            //    let p, q = Rational.numerator n, Rational.denominator n
            //    let r = c.Imaginary ** p * imaginaryPower (Expression.toInt p)
            //    r ** (1Q / q)
            //else
                c.Imaginary ** n * imaginaryPower (Expression.toInt n)
        else
            let r = Expression.simplify c.Magnitude
            let angle = c.Phase

            r ** n
            * Complex(
                cos (n * angle)
                |> Expression.simplifyaux true false
                |> Trigonometric.simplify
                |> Trigonometry.simplifyWithTable,
                sin (n * angle)
                |> Expression.simplifyaux true false
                |> Trigonometric.simplify
                |> Trigonometry.simplifyWithTable
            )

    static member Exp(c: Complex) =
        let r = c.Magnitude
        let theta = c.Phase
        r * Operators.exp (theta * Constant Constant.I)
    
    /// <summary>
    /// Simplifies the complex number.
    /// </summary>
    /// <returns>The simplified complex number.</returns>
    member c.FullSimplify() =
        Complex(Expression.fullerSimplify r, Expression.fullerSimplify i)

    member c.Simplify() =
        Complex(Expression.simplify (Trigonometry.simplify r), Expression.simplify (Trigonometry.simplify i))

    /// <summary>
    /// Creates a new complex number with the specified real part and zero imaginary part.
    /// </summary>
    /// <param name="r">The real part of the complex number.</param>
    new(r) = Complex(r, 0Q)

    /// <summary>
    /// Adds the complex number and the expression.
    /// </summary>
    /// <param name="a">The complex number to add.</param>
    /// <param name="b">The expression to add.</param>
    /// <returns>The sum of the complex number and the expression.</returns>
    static member (+)(a: Complex, b: Expression) = Complex(a.Real + b, a.Imaginary)

    /// <summary>
    /// Adds the expression and the complex number.
    /// </summary>
    /// <param name="a">The expression to add.</param>
    /// <param name="b">The complex number to add.</param>
    /// <returns>The sum of the expression and the complex number.</returns>
    static member (+)(a: Expression, b: Complex) = Complex(a + b.Real, b.Imaginary)

    /// <summary>
    /// Adds two complex numbers.
    /// </summary>
    /// <param name="a">The first complex number to add.</param>
    /// <param name="b">The second complex number to add.</param>
    /// <returns>The sum of the two complex numbers.</returns>
    static member (+)(a: Complex, b: Complex) =
        Complex(a.Real + b.Real, a.Imaginary + b.Imaginary)

    /// <summary>
    /// Subtracts the expression from the complex number.
    /// </summary>
    /// <param name="a">The complex number to subtract from.</param>
    /// <param name="b">The expression to subtract.</param>
    /// <returns>The difference between the complex number and the expression.</returns>
    static member (-)(a: Complex, b: Expression) = Complex(a.Real - b, a.Imaginary)

    /// <summary>
    /// Subtracts the complex number from the expression.
    /// </summary>
    /// <param name="a">The expression to subtract from.</param>
    /// <param name="b">The complex number to subtract.</param>
    /// <returns>The difference between the expression and the complex number.</returns>
    static member (-)(a: Expression, b: Complex) = Complex(a - b.Real, b.Imaginary)

    /// <summary>
    /// Subtracts two complex numbers.
    /// </summary>
    /// <param name="a">The first complex number to subtract.</param>
    /// <param name="b">The second complex number to subtract.</param>
    /// <returns>The difference between the two complex numbers.</returns>
    static member (-)(a: Complex, b: Complex) =
        Complex(a.Real - b.Real, a.Imaginary - b.Imaginary)

    /// <summary>
    /// Multiplies two complex numbers.
    /// </summary>
    /// <param name="a">The first complex number to multiply.</param>
    /// <param name="b">The second complex number to multiply.</param>
    /// <returns>The product of the two complex numbers.</returns>
    static member (*)(a: Complex, b: Complex) =
        Complex(a.Real * b.Real - a.Imaginary * b.Imaginary, a.Imaginary * b.Real + a.Real * b.Imaginary)

    /// <summary>
    /// Multiplies the complex number and the expression.
    /// </summary>
    /// <param name="a">The complex number to multiply.</param>
    /// <param name="b">The expression to multiply.</param>
    /// <returns>The product of the complex number and the expression.</returns>
    static member (*)(a: Complex, b: Expression) = Complex(a.Real * b, a.Imaginary * b)

    /// <summary>
    /// Multiplies the expression and the complex number.
    /// </summary>
    /// <param name="a">The expression to multiply.</param>
    /// <param name="b">The complex number to multiply.</param>
    /// <returns>The product of the expression and the complex number.</returns>
    static member (*)(a: Expression, b: Complex) = Complex(a * b.Real, a * b.Imaginary)

    static member (*)(a: Complex, b: int) = Complex(a.Real * b, a.Imaginary * b)

    static member (*)(a: int, b: Complex) = Complex(a * b.Real, a * b.Imaginary)

    static member (*)(a: Complex, b: float) = Complex(a.Real * b, a.Imaginary * b)

    static member (*)(a: float, b: Complex) = Complex(a * b.Real, a * b.Imaginary)

    /// <summary>
    /// Divides the complex number by the expression.
    /// </summary>
    /// <param name="a">The complex number to divide.</param>
    /// <param name="b">The expression to divide by.</param>
    /// <returns>The quotient of the complex number and the expression.</returns>
    static member (/)(a: Complex, b: Expression) = Complex(a.Real / b, a.Imaginary / b)

    /// <summary>
    /// Divides two complex numbers.
    /// </summary>
    /// <param name="a">The numerator complex number.</param>
    /// <param name="b">The denominator complex number.</param>
    /// <returns>The quotient of the two complex numbers.</returns>
    static member (/)(a: Complex, b: Complex) =
        let conj = b.Conjugate
        (a * conj) / (b * conj).Real

    /// <summary>
    /// Divides the expression by the complex number.
    /// </summary>
    /// <param name="a">The expression to divide.</param>
    /// <param name="b">The complex number to divide by.</param>
    /// <returns>The quotient of the expression and the complex number.</returns>
    static member (/)(a: Expression, b: Complex) = (Complex a) / b

    static member i = Complex(0Q, 1Q)
     
    /// <summary>
    /// Returns a string that represents the complex number.
    /// </summary>
    /// <returns>A string representation of the complex number.</returns>
    override t.ToString() =
        let i, useparens =
            if Utils.expressionFormat = "Infix" then
                "ⅈ", ("(", ")")
            else
                "i", ("\\left(", "\\right)")

        match t.Real, t.Imaginary with
        | c when c = (0Q, 0Q) -> sprintf "0"
        | r, _ when r = 0Q -> sprintf "%s%s" (t.Imaginary.ToFormattedString()) i
        | _, i when i = 0Q -> sprintf "%s" (t.Real.ToFormattedString())
        | _, Number n when n = 1N -> sprintf "%s + %s" (t.Real.ToFormattedString()) i
        | _, Number _
        | _, Identifier _ -> sprintf "%s + %s%s" (t.Real.ToFormattedString()) (t.Imaginary.ToFormattedString()) i
        | _ ->
            let lparens, rparens = if t.Imaginary = 0Q then "", "" else useparens
            sprintf "%s + %s%s%s%s" (t.Real.ToFormattedString()) i lparens (t.Imaginary.ToFormattedString()) rparens

    /// <summary>
    /// Returns a hash code for the complex number.
    /// </summary>
    /// <returns>A hash code for the complex number.</returns>
    override t.GetHashCode() = hash (t.Real, t.Imaginary)

    /// <summary>
    /// Determines whether the specified object is equal to the complex number.
    /// </summary>
    /// <param name="b">The object to compare to the complex number.</param>
    /// <returns>True if the object is equal to the complex number, false otherwise.</returns>
    override x.Equals(b) =
        match b with
        | :? Complex as y -> (x.Real, x.Imaginary) = (y.Real, y.Imaginary)
        | _ -> false

    interface IAdditiveIdentity<Complex, Complex> with
        static member AdditiveIdentity = Complex(0Q, 0Q)
    
    interface IMultiplicativeIdentity<Complex, Complex> with
        static member MultiplicativeIdentity = Complex(1Q, 0Q)

    interface IUnaryNegationOperators<Complex, Complex> with
        static member (~-) (a: Complex) = Complex(-a.Real, -a.Imaginary)
    
    interface IAdditionOperators<Complex, Complex, Complex> with
        static member (+) (a: Complex, b: Complex) = a + b 

    interface IMultiplyOperators<Complex, Complex, Complex> with
        static member (*) (a: Complex, b: Complex) = a * b

    interface IDivisionOperators<Complex, Complex, Complex> with
        static member (/) (a: Complex, b: Complex) = a / b
 

/// <summary>
/// Contains utility functions for working with complex numbers.
/// </summary>
module Complex =
    open Utils
    open System

    /// <summary>
    /// Imaginary unit.
    /// </summary>
    let i = Complex(0Q, 1Q)

    let apply f (c: Complex) = Complex(f c.Real, f c.Imaginary)

    let magnitude (c: Complex) = c.Magnitude

    let ofNumericsComplex (c: Numerics.Complex) = Complex(c.Real, c.Imaginary)

    let ToNumericsComplex (c: Complex) =
        match Expression.toFloat c.Real, Expression.toFloat c.Imaginary with
        | Some r, Some i -> Some(Numerics.Complex(r, i))
        | _ -> None 

    let ofPolar r theta = Complex(r * cos theta, r * sin theta)

    let simplify (c: Complex) = c.Simplify()

    /// <summary>
    /// Given a complex number, returns the expression that represents it.
    /// </summary>
    /// <param name="c">The complex number to convert to an expression.</param>
    /// <returns>The expression that represents the complex number.</returns>
    let toExpression (c: Complex) = c.Real + (c.Imaginary * Constants.i)

    /// <summary>
    /// Splits an `Expression` that represents a complex number into two expressions, one representing the real part and the other representing the imaginary part.
    /// This is done by partitioning according to how the imaginary constant `i` occurs in a sum and if there is no sum, whether it is present in the expression or not.
    /// </summary>
    /// <param name="e">The `Expression` to split.</param>
    /// <returns>A tuple containing the real and imaginary parts of the expression.</returns>
    let splitToRealImaginary (e: Expression) =
        match e with
        | Sum l ->
            let l', cl' = List.partition (Expression.contains Constants.i >> not) l
            Sum l', Sum cl'
        //handle case of just an imaginary number
        | e when Expression.contains Constants.i e -> 0Q, e
        | _ -> e, 0Q

    /// <summary>
    /// Given an expression that represents a complex number, returns the real part of the expression.
    /// </summary>
    /// <param name="e">The expression to get the real part of.</param>
    /// <returns>The real part of the expression.</returns>
    let getRealFromExpression (e: Expression) = splitToRealImaginary e |> fst

    /// <summary>
    /// Given an expression that represents a complex number, returns the imaginary part of the expression.
    /// </summary>
    /// <param name="e">The expression to get the imaginary part of.</param>
    /// <returns>The imaginary part of the expression.</returns>
    let getImaginaryFromExpression (e: Expression) = splitToRealImaginary e |> snd


    /// <summary>
    /// Converts the expression to a complex number.
    /// </summary>
    /// <param name="e">The expression to convert.</param>
    /// <returns>The complex number.</returns>
    let ofExpression (e: Expression) =
        let real, imaginary = splitToRealImaginary e
        Complex(real, imaginary / Constants.i)

    /// <summary>
    /// Returns the imaginary power of i. It uses the rules of powers of i (powers of i have a simple pattern with a cycle of 4) to simplify the expression.
    /// </summary>
    /// <param name="n">The power of i.</param>
    /// <returns>The simplified imaginary power of i.</returns>
    let imaginaryPowerExpression n =
        let effectiveN = (abs n) % 4

        let i =
            match effectiveN with
            | 0 -> 1Q
            | 1 -> Constants.i
            | 2 -> -1Q
            | 3 -> -Constants.i
            | _ -> 1Q

        if n < 0 then 1 / i else i


    /// <summary>
    /// Simplifies the given expression with the assumption that it is a complex number.
    /// Complex numbers are multiplied with FOIL. Expand it, replace i^2 with -1 and simplify.
    /// </summary>
    /// <param name="x"></param>
    /// <returns>The simplified expression.</returns>
    let simplifyExpression x =
        x
        |> recmap (function
            | SquareRoot(IsRealNumber(IsNegativeNumber e)) -> Constants.i * sqrt (-e) //negative square roots are imaginary.
            | Power(IsRealNumber(IsNegativeNumber e), Number n) when n.Denominator = 2I ->
                (Constants.i * sqrt (-e)) ** Operators.fromInteger n.Numerator
            | x -> x)
        |> Algebraic.expand
        |> recmap (function
            | (Power(Constant Constant.I, Number n)) -> imaginaryPowerExpression (int n)
            | x -> x)
        |> Expression.fullSimplify
        |> Algebraic.groupInSumWith Constants.i
        |> Expression.simplify

    /// <summary>
    /// Converts the expression into trigonometric or cis form, that is, a complex number in the form r*(cos(theta) + i*sin(theta))
    /// </summary>
    /// <param name="e"></param>
    let toTrigFormExpression (e: Expression) = (ofExpression e).ToTrigFormExpression()

    /// <summary>
    /// Converts the expression into Euler form, that is, a complex number in the form r*e^(i*theta).
    /// </summary>
    /// <param name="e"></param>
    let toEulerFormExpression (e: Expression) =
        (ofExpression e).ToEulerFormExpression()
