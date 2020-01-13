#load "maths.fsx"
open MathNet.Numerics
open Prelude.Common
open System
open MathNet.Symbolics.Core
open MathNet.Symbolics
open MathNet.Symbolics.Core.Vars
open MathNet.Symbolics.Operators
open MathNet.Symbolics.Utils
open XPlot.Plotly
open MathNet.Symbolics.Differentiation
open Maths

open MathNet.Symbolics.LinearAlgebra
open MathNet.Symbolics.Complex

#I @"C:\Users\cybernetic\source\repos\Simple-Symbolics\Simple-Symbolics\bin\Release\net47"
#r @"MathNet.Numerics.dll"
#r @"MathNet.Numerics.Fsharp.dll"
#r @"MathNet.Symbolic.Ext.dll"
#r "Simple-Symbolics.dll"

setLatex()

//%% markdown
//# Differentials

//The concept of diffferentials is where the historical baggage of calculus seeps through. Specifically, differentials have multiple meanings which must be disambiguated in context. In one context, notations like $dy/dx$ are from limits of fractions and are not themselves fractions. In fact, in typical use, $dy/dx$ is more properly considered a (higher order) function. Leibniz notation is a poor notation for a function but a great notation for intuition. Net: win. [MARGIN]Alternatively, $dy/dx$ really can be considered a fraction built from infinitesimals but then we are no longer dealing with just the reals. There is also a notion of inifinitesimal differentials built up in synthetic differential geometry but this sentence is the extent of my knowledge of the topic.[/MARGIN]

//Such inifinitesimal differentials can often be intuitively treated like fractions without repruccution and was how the subject proceeded historically.

//But note, this notion of differentials corresponds to curried function parameters in our implementation. Treating the operator/function like a fraction forgets this important distinction; when put that way it clearly doesn't make sense to declare its parameters as defining fractions. It is nonetheless a powerful intuition boost.

//In other (most) contexts (such as in linear approximation), the differentials are actually small real numbers (but are still the output of a function application) and while the notation is chosen to correspond to Leibniz's, they are in actual fact quite different. Due to shared concepts (about derivatives based on derivation from limits of small changes), having them coincide makes sense but does create a hostile intution terrain for a beginner. It's a UI trade-off that favors the expert.

//# Differentials as Linear approximations

//[MARGIN]Thermodynamics is one place of importance where they crop up frequently[/MARGIN]
//Differentials have many uses and can be a start on understanding differential forms, jacobians and pushforwards. One key use is for linear approximations at a point by noting how small changes in variables (captured by say, $dx$ or $dy$) propagate thru the function.

//Most generally, they are a generalization of the notion of 1 dimensional derivatives that have good properties for high dimensional functions with interacting variables.

//To compute a (total) differential, we need to find all the variables of an expression.

//%% code
let fx = (x*y + z)

let exprsvars = findVariablesOfExpression fx

exprsvars

//%% markdown
//Then we take the partial derivative of the function with respect to all the variables.

// %%code
[for v in exprsvars -> pdiff v fx]
//%% code
[for v in exprsvars -> evalDerivative (pdiff v fx)]
//%% markdown
//Then we take the sum.

// %%code
List.sum [for v in exprsvars -> evalDerivative (pdiff v fx)]

//%% markdown

//But we've forgotten the differentials. The easiest way to proceed is to introduce a variable built from the name of the variable which we are (partially) differentiating against at each position of the list.

//[MARGIN]This level of detail is typically left silent and automatically handled in the brains of humans[/MARGIN]

// %%code
[for v in exprsvars -> symbol ("d" + symbolString v) * (pdiff v fx)]
//%% code
let totdiffs =
    [ for v in exprsvars ->
          symbol ("d" + symbolString v) * evalDerivative (pdiff v fx) ]

totdiffs
//%% code
List.sum totdiffs

//%% markdown
//Putting it all into a function:

//%% code
let totalDerivative fx =
    let exprsvars = findVariablesOfExpression fx
    List.sum
        [ for v in exprsvars -> symbol ("d" + symbolString v) * (pdiff v fx) ]

totalDerivative fx |> Dx
//%% code
// A function from: http://tutorial.math.lamar.edu/Classes/CalcIII/Differentials.aspx

totalDerivative fx |> Dx
//%% code
(t **3 * r**6) / s**2 |> totalDerivative
//%% code
(t **3 * r**6) / s**2 |> totalDerivative |> Dx

//%% markdown
//Notice that our symbolic math system is treating differentials like normal variables. This should be fine in most contexts however.

//# Differentials of a Function in 1D

//If you do not already know them, it's worth checking the [wikipedia definition of differentials](https://en.wikipedia.org/wiki/Differential_of_a_function#Definition).

//It's fairly opaque, I think. Let's try doing it in code, thereby enforcing clarity. The definition of a differential is it takes a function and a $\Delta x$ and returns the derivative of that function multipled by $\Delta x$. To programatically implement this function, we need to get the variable against which the derivative is taken. Since the function here is 1 dimensional, we can simply extract the first variable without ambiguity. These sort of details are taken for granted in human math.

//%% code
let deltax = V"\\Delta x"

let df Δx x =
    let dx = getFirstVariable x
    diff dx x * Δx

//%% markdown
//Applying this to the identity function, a line: $x \mapsto x$, but which we'll  write as the expression $x$, you get:
//%% code
df deltax x

//%% markdown
//Whose derivative is just:
//%% code
df deltax x |> Dx

//%% markdown
//Therefore we can say: `df Δx x = Δx`. The convention is to use `d` and not `df` and the Δx is kept silent to be worked out in context (we could view it as a partial applicaiton: `d x = df Δx x`) allowing `d x = Δx.` Or `dx = Δx`. The `dx` is in fact $x$ being applied to the function `d`. This notational hackery allows one to relate differentials to derivatives.

//In the below, 'funcx' defines a function with a name as a string and accepts any expression as its input. We can use this to simulate the differential notation and divide through to relate it with the derivative:

//%% code
let dy = funcx "d"
let dx = V"dx"

[ eqapply (replaceSymbols [ deltax, dy x ])
  eqapplys
      ("Pretend $\\operatorname{{d}}(x)$ is not a function",
       replaceExpression dx (dy x))
  eqapply (fun e -> e / dx) ]
|> equationTrace (dy (fx x) <=> df deltax (fx x))

//%% markdown
//## A Simple Derivation

//It's instructive to look at a simple case to build intuition for the previous function definition. The purpose of differentials is to serve as a linear approximation of a function. At a zoomed enough level, these can be fairly good. In 1D, one can locally approximate a function with a line: $y = f'(x)(x-c) + f(c)$ where $f'(x)$ is the derivative or slope of the target function and c is a known nearby point to x. This [section of an online calculus text](https://math.libretexts.org/Bookshelves/Calculus/Book%3A_Calculus_(Apex)/4%3A_Applications_of_the_Derivative/4.4%3A_Differentials) offers a good explanation for why.

//A change in x results in a change in y: $\Delta y = f(x + \Delta x) - f(x)$. When $\Delta x$ is small then the linear approximation is good. We can now derive the following for a known point $c$ and noting that $dy \approx \Delta y$:

//%% code
//The function can be written like this:
let linearProper dx f c x = diff dx (f c) * (x - c) + f c

//but we will use this version as the hold function isolates
//an expression to prevent automated simplifications.
let linear dx f c x = hold(diff dx (f c)) * (hold x - hold c) + hold(f c)

let deltay = V"\\Delta y"
[ eqapply
      (replaceSymbols [ deltay, V "dy" ]
      //false here prevents simplification on replacement
       >> replaceExpressionRaw false (linear x fx c (deltax + c))
              (fx (x + deltax)))
  eqapply Expression.Simplify
  eqapply (replaceSymbol x c) ]
|> equationTrace (deltay <=> fx (x + deltax) - fx c)
