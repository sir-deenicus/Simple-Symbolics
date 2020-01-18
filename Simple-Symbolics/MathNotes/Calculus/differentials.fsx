(*** hide ***)

#r @"C:\Users\cybernetic\source\repos\Prelude\Prelude\bin\Release\net47\prelude.dll"
#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\bin\Release\net47"
#I @"C:\Users\cybernetic\.nuget\packages\"
#r @"fsharp.data\3.3.2\lib\net45\FSharp.Data.DesignTime.dll"
#r @"fsharp.data\3.3.2\lib\net45\FSharp.Data.dll"
#r @"MathNet.Numerics.dll"
#r @"MathNet.Numerics.Fsharp.dll"
#r @"MathNet.Symbolic.Ext.dll"
#r "Simple-Symbolics.dll"
open MathNet.Numerics
open Prelude.Common
open System
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Operators
open MathNet.Symbolics.Utils
open MathNet.Symbolics.Differentiation
open MathNet.Symbolics.LinearAlgebra
open MathNet.Symbolics.Complex

setLatex()

(**
# Differentials

_January 11, 2020_

The concept of differentials is where the historical baggage of calculus seeps through. Specifically, differentials have multiple meanings which must be disambiguated in context. In one context, notations like $dy/dx$ are from limits of fractions and are not themselves fractions. In fact, in typical use, $dy/dx$ is more properly considered a (higher order) function. Leibniz notation is a poor notation for a function but a great notation for intuition. Net: win. [MARGIN]Alternatively, $dy/dx$ really can be considered a fraction built from infinitesimals but then we are no longer dealing with just the reals. There is also a notion of infinitesimal differentials built up in synthetic differential geometry but this sentence is the extent of my knowledge of the topic.[/MARGIN]

Such infinitesimal differentials can often be intuitively treated like fractions without repercussion and was how the subject proceeded historically.

But note, this notion of differentials corresponds to curried function parameters in our implementation. Treating the operator/function like a fraction forgets this important distinction; when put that way it clearly doesn't make sense to declare its parameters as defining fractions. It is nonetheless a powerful intuition boost.

In other (most) contexts (such as in linear approximation), the differentials are actually small real numbers (but are still the output of a function application) and while the notation is chosen to correspond to Leibniz's, they are in actual fact quite different. Due to shared concepts (about derivatives based on derivation from limits of small changes), having them coincide makes sense but does create a hostile intuition terrain for a beginner. It's a UI trade-off that favors the expert.

# Differentials as Linear approximations

[MARGIN]Thermodynamics is one place of importance where they crop up frequently[/MARGIN]

Differentials have many uses and can be a start on understanding differential forms, jacobians and pushforwards. One key use is for linear approximations at a point by noting how small changes in variables (captured by say, $dx$ or $dy$) propagate thru the function.

Most generally, they are a generalization of the notion of 1 dimensional derivatives that have good properties for high dimensional functions with interacting variables.

To compute a (total) differential, we need to find all the variables of an expression.

*)
(*** define-output:out1 ***)
let expr = (x*y + z)
let exprsvars = findVariablesOfExpression expr
exprsvars

(*** include-it:out1 ***)
(**
Then we take the partial derivative of the function with respect to all the variables.

*)
(*** define-output:out2 ***)
[for v in exprsvars -> pdiff v expr]
(*** include-it:out2 ***)
(*** define-output:out3 ***)
[for v in exprsvars -> evalDerivative (pdiff v expr)]
(*** include-it:out3 ***)
(**
Then we take the sum.

*)
(*** define-output:out4 ***)
List.sum [for v in exprsvars -> evalDerivative (pdiff v expr)]

(*** include-it:out4 ***)
(**
But we've forgotten the differentials. The easiest way to proceed is to introduce a variable built from the name of the variable which we are (partially) differentiating against at each position of the list.

[MARGIN]This level of detail is typically left silent and automatically handled in the brains of humans[/MARGIN]

*)
(*** define-output:out5 ***)
[for v in exprsvars -> symbol ("d" + symbolString v) * (pdiff v expr)]
(*** include-it:out5 ***)
(*** define-output:out6 ***)
let totdiffs =
    [ for v in exprsvars ->
          symbol ("d" + symbolString v) * evalDerivative (pdiff v expr) ]

totdiffs
(*** include-it:out6 ***)
(*** define-output:out7 ***)
List.sum totdiffs

(*** include-it:out7 ***)
(**
Putting it all into a function:

*)
(*** define-output:out8 ***)
let totalDerivative expr =
    let exprsvars = findVariablesOfExpression expr
    List.sum
        [ for v in exprsvars -> symbol ("d" + symbolString v) * (pdiff v expr) ]

totalDerivative expr |> Dx
(*** include-it:out8 ***)

(*** define-output:out10 ***)
//A function from: http://tutorial.math.lamar.edu/Classes/CalcIII/Differentials.aspx
(t **3 * r**6) / s**2 |> totalDerivative
(*** include-it:out10 ***)
(*** define-output:out11 ***)
(t **3 * r**6) / s**2 |> totalDerivative |> Dx

(*** include-it:out11 ***)
(**
Notice that our symbolic math system is treating differentials like normal variables. This should be fine in most contexts however.

# Differentials of a Function in 1D

If you do not already know them, it's worth checking the [wikipedia definition of differentials](https://en.wikipedia.org/wiki/Differential_of_a_function#Definition).

[MARGIN]I will deviate a bit because the typical math definition elides parameters that can't be ignored while maintaining generality when implemented on the computer.[/MARGIN]

It's fairly opaque, I think. Let's try doing it in code, thereby enforcing clarity. The definition of a differential is it takes a function and a $\Delta x$ and returns the derivative of that function multiplied by $\Delta x$. To programmatically implement this function, we need to get the variable against which the derivative is taken. Since the function here is 1 dimensional, we can simply extract the first variable without ambiguity. These sort of details are taken for granted in human math.

*)
let deltax = V"\\Delta x"
let df Δx x =
    let dx = getFirstVariable x
    diff dx x * Δx
(**
Applying this to the identity function, a line: $x \mapsto x$, but which we'll  write as the expression $x$, you get:
*)
(*** define-output:out13 ***)
df deltax x

(*** include-it:out13 ***)
(**
Whose derivative is just:
*)
(*** define-output:out14 ***)
df deltax x |> Dx

(*** include-it:out14 ***)
(**
Therefore we can say: `df Δx x = Δx`. The convention is to use `d` and not `df` and the Δx is kept silent to be worked out in context (we could view it as a partial application: `d x = df Δx x`) allowing `d x = Δx.` Or `dx = Δx`. The `dx` is in fact $x$ being applied to the function `d`. This notational hackery allows one to relate differentials to derivatives.

In the below, `funcx` defines a function with a name as a string and accepts any expression as its input. We can use this to simulate the differential notation and divide through to relate it with the derivative:

*)
(*** define-output:out15 ***)
let dy = funcx "d"
let dx = V"dx"
[ eqapply (replaceSymbols [ deltax, dy x ])
  eqapplys
      ("Pretend $\\operatorname{{d}}(x)$ is not a function",
       replaceExpression dx (dy x))
  eqapply (fun e -> e / dx) ]
|> equationTrace (dy (fx x) <=> df deltax (fx x))

(*** include-it:out15 ***)
(**
## A Simple Derivation

It's instructive to look at a simple case to build intuition for the previous function definition. The purpose of differentials is to serve as a linear approximation of a function. At a zoomed enough level, these can be fairly good. In 1D, one can locally approximate a function with a line: $y = f'(x)(x-c) + f(c)$ where $f'(x)$ is the derivative or slope of the target function and c is a known nearby point to x. This [section of an online calculus text](https://math.libretexts.org/Bookshelves/Calculus/Book%3A_Calculus_(Apex)/4%3A_Applications_of_the_Derivative/4.4%3A_Differentials) offers a good explanation for why.

A change in x results in a change in y: $\Delta y = f(x + \Delta x) - f(x)$. When $\Delta x$ is small then the linear approximation is good. We can now derive the following for a known point $c$ and noting that $dy \approx \Delta y$:

*)
(*** define-output:out16 ***)
//The function can be written like this:
let linearProper dx f c x = diff dx (f c) * (x - c) + f c

//but we will use this version as the hold function isolates
//an expression to prevent automated simplifications.
let linear dx f c x = hold(diff dx (f c)) * (hold x - hold c) + hold(f c)

let deltay = V"\\Delta y"

[ eqapplys
    (@"$dy \approx \Delta y$ and approximate $f(x + \Delta x)$ with $f'(x)(x-c) + f(c)$",
       replaceSymbols [ deltay, V "dy" ]
      //false here prevents simplification on replacement
       >> replaceExpressionRaw false (linear x fx c (deltax + c))
              (fx (x + deltax)))
  eqapply Expression.Simplify
  eqapply (replaceSymbol x c) ]
|> equationTrace (deltay <=> fx (x + deltax) - fx c)
(*** include-it:out16 ***)
