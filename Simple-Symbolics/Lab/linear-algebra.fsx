#load "Core.fsx"

open MathNet.Symbolics 
open Core

let inline dot a b = List.map2 (*) a b |> List.sum

let inline vecmatrixmult (v:_ list) (m:_ list list) =
   [for r in List.transpose m -> dot v r] 

let inline matrixvecmult (m:_ list list) (v:_ list) =
   [for r in m -> dot v r] 

let formatGeneric (e:obj) = 
    match e with
     | :? Expression as ex -> Infix.format ex 
     | _ -> string e

type Vector< 'a >(l : 'a list) =
    member __.AsList = l
    static member inline (*) (a:Expression,b : Vector<_>) = Vector(List.map ((*) a) b.AsList)
    static member inline (*) (a:Vector<_>,b : Expression) = Vector(List.map ((*) b) a.AsList)
    static member inline (*) (a:Vector<_>,b : Vector<_>) = dot a.AsList b.AsList
    static member inline (-) (a:Vector<_>,b : Vector<_>) = Vector(List.map2 (-) a.AsList b.AsList)
    static member inline (+) (a:Vector<_>,b : Vector<_>) = Vector(List.map2 (+) a.AsList b.AsList)
    override t.ToString() = sprintf "%A" (List.map formatGeneric t.AsList)

module Vector = 
  let toList (v:Vector<_>) = v.AsList
  let map f (v:Vector<_>) = Vector(List.map f v.AsList)

type Matrix<'a>(l : 'a list list) = 
    member __.AsList = l
    static member inline (*) (a:Expression,b : Matrix<_>) = Matrix(List.map (List.map ((*) a)) b.AsList)
    static member inline (*) (a:Matrix<_>,b : Expression) = Matrix(List.map (List.map ((*) b)) a.AsList)
    static member inline (*) (a:Vector<_>,b : Matrix<_>) = Vector(vecmatrixmult a.AsList b.AsList)
    static member inline (*) (a:Matrix<_>,b : Vector<_>) = Vector(matrixvecmult a.AsList b.AsList)
    override t.ToString() = sprintf "\n%s" (String.concat "\n" (List.map (List.map formatGeneric >> String.concat ", ") t.AsList))

module Matrix =
 let toList (m:Matrix<_>) = m.AsList

    
let det2 (a:Expression list list) = a.[0].[0] * a.[1].[1] - a.[0].[1] * a.[1].[0]      

 