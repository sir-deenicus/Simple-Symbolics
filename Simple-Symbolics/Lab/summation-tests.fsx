
PiSigma.Σ(3*a*i**3Q ,1Q,n) |> extractSumConstants |> Structure.recursiveMap simplifySums

PiSigma.Σ(3*a*k**3Q ,k,1Q,n) |> extractSumConstants//|> Structure.recursiveMap simplifySums

PiSigma.Σ(k ,k,1Q,n)  |> simplifySums

    
PiSigma.Σ (choose n k , k, 0Q,n) |> binomialTheorem

PiSigma.Σ (choose (n) k  * y**(n-k) * x ** k, k, 0Q,n)|> binomialTheorem



PiSigma.Σ(1 + 3 * k ,k,1Q,10Q)  |> simplifySums //|> Expression.Simplify

PiSigma.Σ(1 + 3 * k ,k,0Q,10Q)  |> simplifySums// |> Expression.Simplify

  

PiSigma.Σ( exp (k* -b) ,k,0Q,infinity)   |> Structure.recursiveMap Exponents.replaceExpWithE |> Structure.recursiveMap powerRule  |> simplifyInfiniteSumOfPowers  |> replaceSymbol 1Q a  |> Expression.Simplify


PiSigma.Σ(10Q * 3Q ** k ,k,0Q,3Q)  |> simplifySums
PiSigma.Σ(a*n,1Q,n) |> extractSumConstants |> Structure.recursiveMap simplifySums

PiSigma.Σ(c,1Q,n) |>simplifySums
PiSigma.Σ(1Q,1Q,n) |> simplifySums