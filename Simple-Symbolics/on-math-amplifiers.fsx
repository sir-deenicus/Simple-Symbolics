
# What does an amplification Device for Mathematics Look like?

Programming removes ambiguity and thus offers a level of inspectability that language does not allow.

vs Mathematica vs Lean 

[Lean Proof](https://github.com/ImperialCollegeLondon/M4P33/blob/f427bb3057138dc9ca52830f3147d3cec443a85a/src/affine_algebraic_set/V.lean#L335)

Beyond visualization

link to euler diagram paper

math amplification

the importance of steps

forgetting high frequency details or memory as a low pass filter

math as a series of transformations

AI vs IA

knowledge base

Natural language

calculation

mechanic symbolic

Creative problem solving

proofs

mathematical novelty





A simple example
 
log derivation

Arithmetic sum

infinite geometric sum

Sum of k^p

telescopic logarithm

Deriving Bayes Rule

change of base

[ eqapply (fun x -> b ** x |> Expression.Simplify)
  eqapply (log a)
  eqapply Logarithm.powerRule
  Op Equation.swap
  Op(Solving.reArrangeEquation z)
  eqapply (replaceSymbol (log b x) z) ]
|> equationTrace (log b x <=> z)

How to reverse integrals?

[Rational.applyToNumerator (powerRuleRevSwapped true) >> Expression.Simplify;
 Rational.applyToDenominator Algebraic.expand]
|> List.map Op
|> expressionTrace (e** -b/(1 - e** -b))


let S1 = Vector [a ;             (a + d) ;       V"...";  (a + (n-2)*d) ; (a + (n-1)*d)]
let S2 = Vector [(a + (n-1)*d) ; (a + (n-2)*d) ; V"...."; (a + d);         a]

let S1 = Vector [(a + d);      (a + 2 * d) ;   V"...";  (a + (n-1)*d) ;  (a + (n)*d)]
let S2 = Vector [(a + (n)*d) ; (a + (n-1)*d) ; V"...."; (a + 2 * d)  ; (a + d)]

PiSigma.Σ (a+k *d, k,1Q,2Q) |> PiSigma.Evaluate

S1
S2

let cc = (S1 |> Vector.toList |> List.sum) + (S2 |> Vector.toList |> List.sum) |> Expression.FullSimplify //|> Structure.filter (symbolString >> Strings.strcontains "..." >> not) |> Algebraic.consolidateSums2




(S1 + S2) |> Vector.map (Expression.FullSimplify) |> Vector.toList |> List.groupBy id |> List.map fst

(S1 + S2) |> Vector.map (Expression.FullSimplify) |> Vector.toList |> List.groupBy id |> List.map fst |> List.head |> fun x -> n*x/2 |> Structure.recursiveMap (consolidateSums (Array.minBy width))


let i4 = PiSigma (PiSigma.Σ((k+1)**4,k,1Q, n))
i4.Expression
i4.Evaluate([n, 5N]) |> mapList (Expression.Simplify )

let i4b = PiSigma (PiSigma.Σ((k)**4,k,1Q, n))
i4b.Expression
i4b.Evaluate([n, 5N]) 



(n+1)**4 - 1 |> Algebraic.expand
(n+1)**4 - 1 |> Algebraic.expand |> replaceSymbol 5Q n

(n+1)**4 - 1  |> replaceSymbol 5Q n
let pn = 4Q 
[
Equation.ApplyToRight (Structure.recursiveMap Algebraic.expand)
Equation.ApplyToRight (Structure.recursiveMap expandSummation)
Equation.ApplyToRight (Structure.recursiveMap extractSumConstants) 
fun x -> x -  PiSigma.Σ( k**pn ,k,1Q,n) |> Equation.Apply Expression.Simplify

fun x -> x -  pn * PiSigma.Σ( k**(pn-1) ,k,1Q,n)
Equation.ApplyToRight (Structure.recursiveMap simplifySums)

fun x -> x / -pn 
Equation.Apply Expression.FullSimplify]
|> List.map Op
|> equationTrace (PiSigma.Σ( k**pn ,k,1Q,n) <=> PiSigma.Σ( (k+1)**pn ,k,1Q,n) - ((n+1)**pn  - 1))



PiSigma.Σ(ln(1 - 1/(n+1)**2),n,1Q,infinity)