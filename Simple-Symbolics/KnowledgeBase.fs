module MathNet.Symbolics.KnowledgeBase

open MathNet.Symbolics
open MathNet.Symbolics.Core
open MathNet.Symbolics.Utils
open MathNet.Symbolics.Core.Vars
open System.Text
open Prelude.StringMetrics

type Factoid =
    { Equation: Expression * Expression
      Requirements: Requirements list
      Description: string }

    member t.Left = fst t.Equation
    member t.Right = snd t.Equation
    member t.ToDefinition = Definition(t.Left, t.Right, t.Description)

    static member ofTuple(a, r, d) =
        { Equation = a
          Requirements = r
          Description = d }

let Equations =
    [ { Equation = diff x (gammaln x), diff x (gamma x) / (gamma x)
        Requirements = []
        Description = "gamma and digamma" }

      { Equation = choose n k, (n - k + 1) / k * choose n (k - 1Q)
        Requirements = [ IsInteger; IsPositive ]
        Description = "recursive definition of combination/choose" }

      { Equation = gamma n, fac (n - 1)
        Requirements = [ IsInteger ]
        Description = "gamma and factorial" }

      { Equation = erf x, 2 / sqrt (Constants.pi) * defintegral t 0Q x (exp (-t ** 2Q))
        Requirements = []
        Description = "error function integral" }

      Factoid.ofTuple ((beta x y, (gamma x * gamma y) / gamma (x + y)), [], "beta and gamma functions")
      Factoid.ofTuple (
          (incompleteBeta a b x, defintegral t 0Q x (t ** (a - 1) * (1 - t) ** (b - 1))),
          [],
          "incomplete beta integral"
      )
      Factoid.ofTuple (
          (incompleteBeta a b x, regularizedBeta a b x / beta a b),
          [],
          "incomplete beta and regularized beta"
      ) ]


let factoidsToTable (factoids: (Factoid * float) seq) =
    [| for (f, w) in factoids ->
           [| $"{fmt f.Left} = {fmt f.Right}"
              fmttext f.Description
              sprintf ""
              $"Weight: {w}" |] |]

let searchFactoidsByFormula thresh (e: Expression) =
    let strf = string e

    [| for eq in Equations do
           let lstr, rstr = string eq.Left, string eq.Right

           let lscore = Prelude.StringMetrics.stringSimilarityDice strf lstr
           let rscore = Prelude.StringMetrics.stringSimilarityDice strf rstr

           if lscore >= thresh || rscore >= thresh then
               yield eq, max lscore rscore |]

let searchFactoids (str: string) =
    [| for e in Equations do
        if e.Description.Contains(str.ToLower()) then
            yield e |]


module Information = 
    open Equations
    
    let H = probn "H"
    let Hc x y = probcn "H" x y
    let I x y = probparamn "I" x y
    let relentropy p q = Func.fn "D_{KL}" (tuple [ p; q ])

    let ineqs = [leq (I X Y) (H X), "Mutual information bits are not greater than entropy, I(X;Y) <= H(X)"
                 geq (I X Y) (0Q), "Mutual information bits are non-negative, I(X;Y) >= 0"]

    let eqs =
        [ H(tuple [ p; q ]), H p + relentropy p q, "cross entropy in terms of entropy and relative entropy"
          Hc X Y, H X - I X Y, "Conditional entropy in terms of entropy and mutual information"
          Hc X Y, H(tuple [ X; Y ]) - H Y, "Conditional entropy in terms of joint entropy and entropy"
          I X Y, H X + H Y - H(tuple [ X; Y ]), "Mutual information in terms of entropy and joint entropy"
          I X Y, H Y - Hc Y X, "Mutual information in terms of conditional entropy and entropy"
          I X Y, relentropy (prob (tuple [ P[X]; P[Y] ])) (prob P[X] * prob P[Y]), "Mutual information in terms of relative entropy"]
