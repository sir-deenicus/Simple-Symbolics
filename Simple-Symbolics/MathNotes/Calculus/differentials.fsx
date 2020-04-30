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
open Expression
open MathNet.Symbolics.NumberTheory

setLatex()

(**
# Differentials

_January 11, 2020_

The concept of differentials is where the historical baggage of calculus seeps through. Specifically, differentials have multiple meanings which must be disambiguated in context. For example, in one context, notations like $dy/dx$ are actually defined in terms of limits of fractions but are not themselves fractions. In fact, in typical use, $dy/dx$ is more properly considered a (higher order) function. Leibniz notation is a poor notation for a function but a great notation for intuition. Net: win. [MARGIN]Alternatively, $dy/dx$ really can be considered a fraction built from infinitesimals but then we are no longer dealing with just the reals. There is also a notion of infinitesimal differentials built up in synthetic differential geometry but this sentence is the extent of my knowledge of the topic.[/MARGIN]

Differentials as infinitesimals can often be intuitively treated like fractions without repercussion and was how the subject proceeded historically.

In the Leibniz notion of differentials $dy$ and $dx$, $\frac{d}{dx}$ roughly corresponds to the partial application of a symbol $x$, e.g. `diff x`, while the  output of the differential operator is the derivative $\frac{d}{dx}y$ or `diff x y` (with `diff` in this package roughly corresponding to `d` in the Leibniz conception). Although the output is a function, the implicit assumption in many discussions is that some input has already been applied, reducing it to an arbitrary number. $dx$ tells us `x` is the parameter to be passed to `diff`, against which we'll be differentiating and captures the changing (often controllable) input parameter. Treating the differential operator/higher order function like a fraction forgets this important distinction, but although it's misleading to pretend function parameters and outputs are fractions, it is nonetheless a powerful intuition boost.

In most other contexts, differentials are more properly thought of in terms of linear approximations. Here, differentials can really be considered small real numbers (although, differentials grounded in linear approximations are still better generally thought of as functions) and while notation is chosen to correspond to Leibniz's, they are not equivalent. Due to being closely related, having differentials and differentiation notation coincide makes sense. Alas, this is at the cost of more hostile intuition terrain for beginners. It's a UX trade-off that favors the expert.

# Differentials as Linear approximations

[MARGIN]Thermodynamics is one place of importance where they crop up frequently[/MARGIN]

Differentials have many uses and can be a start on understanding differential forms, jacobians and pushforwards. One key use is for linear approximations at a point by noting how small changes in variables (captured by say, $dx$ or $dy$) propagate through the function to yield changes in output.

Total Differentials are a generalization of the notion of 1-dimensional derivatives and capture how perturbations flow through all the dependencies of high dimensional functions of many variables.

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
But we've forgotten the differentials (which can be analogized with forgetting the bases of a vector, a big oops!). The easiest way to proceed is to introduce a variable built from the name of the variable which we are (partially) differentiating against at each position of the list.

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

[MARGIN]`Dx` takes the derivative of only the derivative definitions in the expression[/MARGIN]

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

Notice that our symbolic math system is treating differentials like normal variables. Which is a bit of a problem. It is useful to extract the differentials so they are easier to visually parse out as a sort of basis. To do this, I'll use a simple heuristic to extract a differential symbol. Any two letter variable whose name is *d+symbol*; for example, dx or dy or dξ etc, is extracted.

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
[MARGIN]There are certain tricks required to wrestle the symbolic form that are not required when working on paper but the upside is over time, a powerful library of solution techniques specialized to the user can be built. With even the possibility of automated application by "AI".[/MARGIN]

Thus, in a handful of lines of code, we have defined a total derivative and adjusted its presentation using built in combinators and functions. Unlike with most CAS, the emphasis is largely on a step by step understanding than black box results. This is more a philosophical difference in approach since a system like this can be built in any CAS too. The disadvantage of bigger more complex Computer Algebra packages is the difficulty of custom modifications and the large surface area of things to be understood.

## A Cleaner Improvement

Naturally, after working out the above method, I thought up a simpler way to achieve the same goal: by converting the list of partial derivatives to a vector and then using the Vector library functionality to rewrite in terms of a basis given by a provided list of variable symbols. The modification of the `totalDerivative` function is, rather than multiplying with partial derivative, we seperate the two into a list of differentials and partial derivatives. *)

(*** define-output:out11d ***)
let totalDerivativeB expr =
    let exprsvars = findVariables expr
    let bases, elements =
        [ for v in exprsvars ->
            symbol ("d" + symbolString v), (pdiff v expr) ]
        |> List.unzip
    bases, Vector elements

[ Op(recmap evalDerivative)
  Op(recmap Hold.extractLeadingNegative >> simplifyLite) ]
|> expressionTrace
       (Vector.toBasisExpression (totalDerivativeB ((t ** 3 * r ** 6) / s ** 2)))
(*** include-it:out11d ***)

(**
[MARGIN]Usually, we would use the shorter `Dx` or `D` but those automatically simplify, which removes the expression from isolation.[/MARGIN]

The *recursive map* above recursively evaluates the derivatives contained in an expression and then, like with the previous method, we remove the negative so it's outside the isolated expression.

Having focused on the machinery of total differentials, it is useful to try to get some intuition on what they are.

# Differentials of a Function in 1D

If you do not already know them, it's worth checking the [wikipedia definition of differentials](https://en.wikipedia.org/wiki/Differential_of_a_function#Definition).

[MARGIN]I'll deviate from the wikipedia definition a bit for clarity's and precision's sake. The substance is the same.[/MARGIN]

It's fairly opaque, I think. Let's try doing it in code, thereby enforcing clarity. Our definition of a differential constructing function $d$, is that it takes a single variable function $f$ and returns a function that takes two inputs: an $x$ that's of the same type as $f$'s domain and a $\Delta x$. This new function $df$, the differential, computes the result of multiplying the derivative of $f$ at $x$ with $\Delta x$. Something like:

```
let d f =
    let f' = diff dx f
    fun Δx x -> f'(x) * Δx
```
To programmatically implement this function, we need to get the variable against which the derivative is taken. Since the function here is 1-dimensional, we can simply extract the first variable without ambiguity. These sort of details are taken for granted in human math. The other detail is with regards to defining symbolic mathematical functions as opposed to programmatic ones. `fn` defines a single parameter function with the second parameter an expression representing the body.
*)
let deltax = V"\\Delta x"

let df xvar f =
    let f' = diff xvar f
    fn xvar (fn deltax (f' * deltax))

let d f = df (Expression.getFirstVariable f) f
(**
Applying this to $x$, you get:
*)
(*** define-output:out13 ***)
d x
(*** include-it:out13 ***)
(**
Since the derivative of $x$ is 1, $d(a)(\Delta x)=\Delta x$ for all $a's$. Therefore, the notational abuse is to write $dx$ in lieu of $\Delta x$. Specifically, notice that `d x` ignores all input $x's$ and always returns $\Delta x$. Evaluating the contained derivative:*)
(*** define-output:out14 ***)
D x (d x)
(*** include-it:out14 ***)
(** The same would not be true if the function was $x^2$: *)
(*** define-output:out14b ***)
D x (d (x**2))
(*** include-it:out14b ***)

(**
Now enough is in place to show the standard notation's hostility. This is a bit of notational hackery that is typically employed based on the behavior of $d(x)$. First, bind $d(x)$ as $dx$ keeping in mind that $dx$ is itself a function. Since $dx$ is a constant function of (ignores inputs except) $\Delta x$, one can use $dx$ in place of $\Delta x$.

Thus creating 3 different notions of differential with the *same symbol*! The $dx$ of Leibniz notation, the $dx$ that is the bound function and the $dx$ that is the bound function with an arbitrary input implicitly applied, to be worked out in context--thus a real number (or some other concrete element).

While an expert can navigate and have these carefully separated, this lack of clarification adds unnecessary difficulty when learning the concept. The below is a sketch that tries to emphasize possible steps that are often elided in definitions:
*)
(*** define-output:out15 ***)

[ eqapplys ("apply $x$ as input", applyfn x)
  eqapplys ("apply $\Delta x$ as input", applyfn deltax)
  eqapply (fun x -> x / deltax)
  eqapplys ("d(x) = $\Delta x$", replaceSymbol (d x) deltax)
  eqapply (replaceExpression (func "d" x) (d x))
  eqapplys
      ("bind d(x) output as dx with some $\Delta x$ implicitly applied",
       replaceExpression (V "dx") (func "d" x)) ]
|> equationTrace ((func "d" f) <=> d (fx x))

(*** include-it:out15 ***)
(**
## A Simple Derivation

It's instructive to look at a simple case to build intuition for the previous function definition. The above defined function essentially packages the working out of linear approximations. Next, we'll look at a more manual calculation.

The purpose of differentials is to serve as a linear approximation of a function. It is often useful to approximate the change in  function output value using a linear approximation of the result of a small perturbation added to the function's input; given you know the value at a particular nearby point. At a zoomed enough level, these can be fairly good.

In 1D, one can locally approximate a function $f(x)$ at any point near $x = c$ with a line: $y(\_) = f'(c)(x-c) + f(c)$ where $f'$ is the derivative or *function for slopes*, of the target function. This [section of an online calculus text](https://math.libretexts.org/Bookshelves/Calculus/Book%3A_Calculus_(Apex)/4%3A_Applications_of_the_Derivative/4.4%3A_Differentials) offers a good explanation for why. I'll give a sketch here. Since we want a linear approximation of $f$ near $c$ and we know that the slope of $f$ at any $x$ is given by the derivative, we can proceed as: $y - f(c) = f'(c)(x-c)$ or $y = f'(c)(x-c) + f(c)$.

[MARGIN]$dy$ is a differential, which were more generally defined in the previous section. In this context, it's a quantity approximately equal to $\Delta y$ and comes about because we are using a linear approximation in place of $f(x + \Delta x)$.[/MARGIN]

A change in $x$ results in a change in $y$: $\Delta y = f(x + \Delta x) - f(x)$. When $\Delta x$ is small then the linear approximation of $f(x + \Delta x)$ will also be good. Why go through all this? Linear approximations have utility in optimization, where they provide guidance on how to step (I have italicized some of why this is in the below quote which is extracted from the above linked to calculus text). Another way they're useful is when you know the derivative but not the function itself:

> In "most" real life situations, we do not know the function that describes a particular behavior. Instead, we can only take measurements of how things change -- measurements of the derivative.
>
> Imagine water flowing down a winding channel. It is easy to measure the speed and direction (i.e., the velocity) of water at any location. It is very hard to create a function that describes the overall flow, hence it is hard to predict where a floating object placed at the beginning of the channel will end up. However, we can approximate the path of an object using differentials. Over small intervals, the path taken by a floating object is essentially linear. *Differentials allow us to approximate the true path by piecing together lots of short, linear paths. This technique is called Euler's Method*, studied in introductory Differential Equations courses.

We can now derive the following, noting that $dy \approx \Delta y$:

*)
(*** define-output:out16 ***)
//The function can be written like this:
let linearApprox dx f c x = diff dx (f c) * (x - c) + f c

//but we will use this version as the hold function isolates
//an expression to prevent automated simplifications.
let linear dx f c x = hold(diff dx (f c)) * (hold x - hold c) + hold(f c)

let deltay = V"\\Delta y"

[ eqapplys
    (@"$dy \approx \Delta y$ and approximate $f(x + \Delta x)$",
       replaceSymbols [ deltay, V "dy" ]
      //false here prevents simplification on replacement
       >> Expression.replaceExpressionRaw false (linear x fx x (deltax + x))
              (fx (x + deltax)))
  eqapplys("Simplify", Expression.Simplify) ]
|> equationTrace (deltay <=> fx (x + deltax) - fx x)
(*** include-it:out16 ***)

(**
## A Simple Example

Everything so far has been quite abstract. Here is an example from the Calculus text linked above where $\sqrt{4.5}$ is approximated, using a known value: $\sqrt 4$. Then $dy$ is:
*)

(*** define-output:out17 ***)
List.map Instr [ Dx, "Evaluate derivative"
                 applyfn (real 4.), "$x=4$"
                 applyfn (1 / 2Q), "$\\Delta x = 0.5$" ]
|> expressionTrace (d (sqrt x))
(*** include-it:out17 ***)
(**
And that's it. In higher dimensions, the machinery of linear algebra is often used for representation. With matrix products for composition, differentials as (co)vectors (or single row matrices and more generally, Jacobian matrices). You can even sometimes view dot products as sort of applying the differential (e.g. when applying an increment/delta).

A further generalization is the pushforward, allowing working in more general spaces than say, $\mathbb{R}^{n}$. But the essential idea remains the same as the humble 1D slope based linear approximation.
*)
