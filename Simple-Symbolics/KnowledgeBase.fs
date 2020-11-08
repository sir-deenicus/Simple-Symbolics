module KnowledgeBase

open MathNet.Symbolics
open MathNet.Symbolics.Core
open MathNet.Symbolics.Utils
open MathNet.Symbolics.Core.Vars
open System.Text 

type Factoid =
    { Equation: Expression * Expression
      Requirements: Requirements list
      Description: string } with 
    member t.Left = fst t.Equation
    member t.Right = snd t.Equation
    member t.ToDefinition = Definition(t.Left, t.Right, t.Description)
    static member ofTuple(a,r,d) = {Equation = a; Requirements = r; Description = d}
 
let Equations =
    [ { Equation = diff x (gammaln x), diff x (gamma x) / (gamma x)
        Requirements = []
        Description = "gamma and digamma" }
      
      { Equation = choose n k, (n - k + 1) / k * choose n (k-1Q)
        Requirements = [ IsInteger; IsPositive ]
        Description = "recursive definition of combination/choose"}
      
      { Equation = gamma n, fac (n - 1)
        Requirements = [ IsInteger ]
        Description = "gamma and factorial" }

      { Equation = erf x, 2/sqrt(Constants.pi) * defintegral t 0Q x (exp (-t **2Q))
        Requirements = []
        Description = "error function integral" }  
      
      Factoid.ofTuple ((beta x y, (gamma x * gamma y)/gamma (x+y)), [], "beta and gamma functions")
      Factoid.ofTuple ((incompleteBeta a b x, defintegral t 0Q x (t **(a-1) * (1-t)**(b-1))), [], "incomplete beta integral")
      Factoid.ofTuple ((incompleteBeta a b x, regularizedBeta a b x / beta a b), [], "incomplete beta and regularized beta")]

let printFactoids (facts: Factoid seq) =
    let sb = StringBuilder()

    for fact in facts do
        sprintf
            "%s = %s | Requirements %A | Description: %s\n"
            (fmt (fst fact.Equation))
            (fmt (snd fact.Equation))
            fact.Requirements
            fact.Description
        |> sb.AppendLine
        |> ignore

    sb.ToString()

open Prelude.StringMetrics

let searchFactoidsByFormula thresh (e: Expression) =
    let strf = Infix.format e
    [| for eq in Equations do
        let lstr, rstr =
            Infix.format eq.Left, Infix.format eq.Right

        let score = stringSimilarityDice strf lstr
        if score >= thresh then
            yield eq, score
        else
            let score2 = stringSimilarityDice strf rstr
            if score2 >= thresh then yield eq, score2 |]

let searchFactoids (str:string) = 
    [|for e in Equations do if e.Description.Contains (str.ToLower()) then yield e|]