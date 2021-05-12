module MathNet.Symbolics.ProbabilityDistributions

open MathNet.Symbolics
open MathNet.Symbolics.Core
open MathNet.Symbolics.Utils
open MathNet.Symbolics.Core.Vars
open System.Text
open MathNet.Symbolics.Operators

type IProbabilityDistribution =
    abstract ExpectedValue : Expression
    abstract Entropy : Expression
    abstract Mode : Expression
    abstract Variance : Expression
    abstract Median : Expression
    abstract CDF : Expression
    abstract Description : string
    abstract Requirements : (Requirements * Expression * string) list

type IDiscreteDistribution =
    inherit IProbabilityDistribution
    abstract PMF :  Expression

type IContinuousDistribution =
    inherit IProbabilityDistribution
    abstract PDF :  Expression

///From wiki:binomal with distr with parameters n and p is the discrete probability distribution of the number of successes in a sequence of n independent experiments, each asking a yes–no question, and each with its own Boolean-valued outcome: success/yes/true/one (with probability p)
type Binomial(n,p) =
    let q = 1Q - p
    let pmf k = choose n k * p ** k * q ** (n-k)
    ///Probability of k Heads in n flips each with probability p
    member p.Prob k = pmf k
    member g.Entropy = 1/2Q * log 2Q (2*Pi * Constants.e * n * p * q)
    member g.Mode = floor ((n+1Q)*p)
    member g.Variance = n * p * q
    member g.Median = ceil (n*p)
    member g.CDF = regularizedBeta (n-k) (1Q+k) q
    member g.ExpectedValue = n * p
    member g.Description = "Wiki: Binomial probability distribution with parameters n and p is the discrete probability distribution of the number of successes in a sequence of n independent experiments, each asking a yes–no question, and each with its own Boolean-valued outcome: success/yes/true/one (with probability p) "
    member g.PMF = pmf k

    interface IDiscreteDistribution with
        member g.Entropy = g.Entropy
        member g.Mode = g.Mode
        member g.Variance = g.Variance
        member g.Median = g.Median
        member g.CDF = g.CDF
        member g.ExpectedValue = g.ExpectedValue
        member g.Description = g.Description
        member g.PMF = g.PMF
        member g.Requirements = []

type Normal(mean,standardDeviation) =
    let variance = standardDeviation ** 2Q
    let pdf x =
        1/(standardDeviation * sqrt (2*Constants.π)) * exp (-1/2Q*((x-mean)/standardDeviation)**2Q)

    member p.Prob x = pdf x
    member g.Entropy = 1/2Q * ln (2 * Constants.π * Constants.e * variance ** 2Q)
    member g.Mode = mean
    member g.Variance = variance
    member g.Median = mean
    member g.CDF = 1/2Q * (1 + erf ((x-mean)/(standardDeviation * sqrt 2Q)))
    member g.ExpectedValue = mean
    member g.Description = "Normal distribution"
    member g.PDF = pdf x

    interface IContinuousDistribution with
        member g.Entropy = g.Entropy
        member g.Mode = g.Mode
        member g.Variance = g.Variance
        member g.Median = g.Median
        member g.CDF = g.CDF
        member g.ExpectedValue = g.ExpectedValue
        member g.Description = g.Description
        member g.PDF = g.PDF
        member g.Requirements = []

/// the exponential distribution is the probability distribution of the time between events in a Poisson point process,
type Exponential(rate) =
    member p.Prob x = rate * exp (-rate*x)
    member g.Entropy = 1Q - ln rate
    member g.Mode = 0Q
    member g.Variance = 1/(rate**2Q)
    member g.Median = ln 2Q/rate
    member g.CDF = 1Q - exp (-rate * x)
    member g.ExpectedValue = 1/rate
    member g.Description = "Exponential distribution, continuous analogue of the geometric distribution"
    member g.PDF = g.Prob x

    interface IContinuousDistribution with
        member g.Entropy = g.Entropy
        member g.Mode = g.Mode
        member g.Variance = g.Variance
        member g.Median = g.Median
        member g.CDF = g.CDF
        member g.ExpectedValue = g.ExpectedValue
        member g.Description = g.Description
        member g.PDF = g.PDF
        member g.Requirements = [IsPositive, rate, sprintf "%s > 0" (fmt rate)]
