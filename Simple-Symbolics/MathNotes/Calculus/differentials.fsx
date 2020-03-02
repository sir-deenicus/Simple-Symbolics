(*** hide ***)
#I @"C:\Users\cybernetic\Jupyter-Notebooks"
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

The concept of differentials is where the historical baggage of calculus seeps through. Specifically, differentials have multiple meanings which must be disambiguated in context. For example, in one context, notations like $dy/dx$ are actually defined in terms of limits of fractions but are not themselves fractions. In fact, in typical use, $dy/dx$ is more properly considered a (higher order) function. Leibniz notation is a poor notation for a function but a great notation for intuition. Net: win. [MARGIN]Alternatively, $dy/dx$ really can be considered a fraction built from infinitesimals but then we are no longer dealing with just the reals. There is also a notion of infinitesimal differentials built up in synthetic differential geometry but this sentence is the extent of my knowledge of the topic.[/MARGIN]

Differentials as infinitesimals can often be intuitively treated like fractions without repercussion and was how the subject proceeded historically.

In the Leibniz notion of differentials $dy$ and $dx$, $dy$ correspond to the output of the differential operator (`diff` in this package, roughly corresponding to `d` in the Leibniz conception). Although the output is a function, the implicit assumption in most discussions is that some input has already been applied, reducing it to say, an arbitrary number. `dx` tells us `x` is the parameter to be passed to `diff`, against which we'll be differentiating and captures the changing quantity. Treating the differential operator/higher order function like a fraction forgets this important distinction; it's clearly (more than) a bit misleading to declare its parameters and outputs as defining fractions. It is nonetheless a powerful intuition boost.

In most other contexts, differentials are more properly thought of in terms of linear approximations. Here, differentials can really be considered small real numbers (not infinitesimals; although, this notion of differential is still more generally thought of as a function) and while notation is chosen to correspond to Leibniz's, they are in actual fact quite different. Due to being closely related, having differentials and differntiation notation coincide makes sense. Alas, this is at the cost of more hostile intuition terrain for beginners. It's a UX trade-off that favors the expert.

# Differentials as Linear approximations

[MARGIN]Thermodynamics is one place of importance where they crop up frequently[/MARGIN]

Differentials have many uses and can be a start on understanding differential forms, jacobians and pushforwards. One key use is for linear approximations at a point by noting how small changes in variables (captured by say, $dx$ or $dy$) propagate through the function.

Most generally, they are a generalization of the notion of 1 dimensional derivatives that have good properties for high dimensional functions many variables.

To compute a (total) differential, we need to find all the variables of an expression.

*)
(*** define-output:out1 ***)
let expr = (x*y + z)
let exprsvars = Expression.findVariables expr
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
    let exprsvars = Expression.findVariables expr
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

## Improving the Presentation

Notice that our symbolic math system is treating differentials like normal variables. While this is no problem, it is useful to extract the differentials so they are easier to visually parse out. To do this, I'll use a simple heuristic to extract a differential symbol. Any two letter variable whose name is *d+symbol*; for example, dx or dy or dξ etc, is extracted.

This is a good heuristic since any violation would make things confusing for the human. It is also rare to find a differential whose naming pattern is different. Unlike with most computer math, presentation is as much a priority as correctness for us: there is a strong expectation of an interactive process between human and machine. *)

let tdiff = (t **3 * r**6) / s**2 |> totalDerivative |> Dx

let getDifferentialSymbol term =
    Structure.recursiveFilter (function
        | Identifier(Symbol s) when s.Length = 2 && s.[0] = 'd' -> true
        | _ -> false) term
    |> Option.get

(**
[MARGIN]`hold` is a function that isolates the input expression, preventing any automatic simplifications or aggregations.[/MARGIN]

Then it simply remains to go through the terms in our sum, dividing each by its differential symbol (thus getting rid of said symbol) then holding/isolating the resulting expression and finally multiplying that result with the differential symbol.*)
(*** define-output:out11b ***)
List.sum
    [ for term in Structure.toList tdiff ->
        let df = getDifferentialSymbol term
        df * (hold (term / df)) ]
(*** include-it:out11b ***)

(** The final step is to extract the negative term out from the isolated expression:*)
(*** define-output:out11c ***)
List.sum
    [ for term in Structure.toList tdiff ->
        let df = getDifferentialSymbol term
        df * Hold.extractLeadingNegative (hold (term / df)) ]
(*** include-it:out11c ***)

(**
[MARGIN]There are certain tricks required to wrestle the symbolic form that are not required when working on paper but the upside is over time, a powerful library of solution techniques sepcialized to the user can be built. With even the possibility of automated application by "AI".[/MARGIN]

Thus, in a handful of lines of code, we have defined a total derivative and adjusted its presentation using built in combinators and functions. Unlike with most CAS, the emphasis is largely on a step by step understanding than black box results. This is more a philosophical difference in approach since a system like this can be built in any CAS too. The disadvantage of bigger more complex Computer Algebra packages is the difficulty of custom modifications and the large surface area of things to be understood.

Having focused on the machinery of total differentials, it is useful to try to get some intuition on what they are.

# Differentials of a Function in 1D

If you do not already know them, it's worth checking the [wikipedia definition of differentials](https://en.wikipedia.org/wiki/Differential_of_a_function#Definition).

It's fairly opaque, I think. Let's try doing it in code, thereby enforcing clarity. The definition of a differential is that it takes a function $f$ and returns a function that takes two inputs, an $x$ thats of the same type as $f$ and a $\Delta x$. This new function $df$, computes the result of multiplying the derivative of $f$ at $x$ with $\Delta x$. Something like:

```
let d f =
    let f' = diff dx f
    fun Δx x -> f'(x) * Δx
```
To programmatically implement this function, we need to get the variable against which the derivative is taken. Since the function here is 1 dimensional, we can simply extract the first variable without ambiguity. These sort of details are taken for granted in human math.

*)
let deltax = V"\\Delta x"


let dy f x =
    let xvar = Expression.getFirstVariable f
    fun Δx x -> (diff xvar f |> replaceSymbol x xvar) * Δx
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
Therefore we can say: `df Δx x = Δx`. The convention is often to use `d` and not `df` and the Δx is kept silent to be worked out in context (we could view this as partial application: `d = df Δx` in point free notation or `d x = df Δx x`), allowing `d x = Δx.` Or `dx = Δx`. The `dx` is in fact $x$ being applied to the function `d`. This notational hackery allows one to relate differentials to derivatives.

In the below, `funcx` symbolically defines a function with a given string as its name and accepts any expression as the input (thus a symbolic but not executable function definition). We can use this to simulate the differential notation and divide through to relate it with the derivative:

*)
(*** define-output:out15 ***)
let dfx = funcx "d"
let dx = V "dx"

[ eqapplys
      ("$\\operatorname{{d}}(x) = \\Delta x$", replaceSymbols [ deltax, dfx x ])
  eqapplys ("Divide through", fun e -> e / dfx x)

  eqapplys
      ("Pretend $\\operatorname{{d}}(x)$ is not a function",
       Expression.replaceExpression dx (dfx x)) ]
|> equationTrace (dfx (fx x) <=> df deltax (fx x))

(*** include-it:out15 ***)
(**
## A Simple Derivation

It's instructive to look at a simple case to build intuition for the previous function definition. The purpose of differentials is to serve as a linear approximation of a function. At a zoomed enough level, these can be fairly good.

In 1D, one can locally approximate a function $f(x)$ at a point $x = c$, with a line: $y(x) = f'(x)(x-c) + f(c)$ where $f'(x)$ is the derivative or *function for slopes*, of the target function and c is a known nearby point to x. This [section of an online calculus text](https://math.libretexts.org/Bookshelves/Calculus/Book%3A_Calculus_(Apex)/4%3A_Applications_of_the_Derivative/4.4%3A_Differentials) offers a good explanation for why. I'll give a sketch here. Since we want a linear approximation of $f$ at $c$ and we know that the slope of $f$ at any $x$ is given by the derivative, we can proceed as: $y - f(c) = f'(c)(x-c)$ or $y = f'(c)(x-c) + f(c)$.

A change in x results in a change in y: $\Delta y = f(x + \Delta x) - f(x)$. When $\Delta x$ is small then the linear approximation of $f(x + \Delta x)$, at some $x$, is good. We can now derive the following, noting that $dy \approx \Delta y$:

*)
(*** define-output:out16 ***)
//The function can be written like this:
let linearApprox dx f c x = diff dx (f c) * (x - c) + f c

//but we will use this version as the hold function isolates
//an expression to prevent automated simplifications.
let linear dx f c x = hold(diff dx (f c)) * (hold x - hold c) + hold(f c)

let deltay = V"\\Delta y"

[ eqapplys
    (@"$dy \approx \Delta y$ and approximate $f(x + \Delta x)$ with $f'(x)(x-c) + f(c)$",
       replaceSymbols [ deltay, V "dy" ]
      //false here prevents simplification on replacement
       >> Expression.replaceExpressionRaw false (linear x fx x (deltax + x))
              (fx (x + deltax)))
  eqapplys("Simplify", Expression.Simplify) ]
|> equationTrace (deltay <=> fx (x + deltax) - fx x)
(*** include-it:out16 ***)
