namespace MathNet.Symbolics

open NumberProperties

type Requirements =
    | IsInteger
    | IsPositive
    override t.ToString() =
        match t with
        | IsInteger -> "Is Integer"
        | IsPositive -> "Positive"
    static member Run = function
        | IsInteger -> Expression.isInteger
        | IsPositive -> Expression.isPositiveExpression