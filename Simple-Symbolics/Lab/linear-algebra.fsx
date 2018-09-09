#load "Core.fsx"

open MathNet.Symbolics 

let inline dot a b =
    List.map2 (*) a b |> List.sum

let inline matrixvec (v:_ list) (m:_ list list) =
   [for r in List.transpose m -> dot v r] 

let det2 (a:Expression list list) = a.[0].[0] * a.[1].[1] - a.[0].[1] * a.[1].[0]      

 