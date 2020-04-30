module MathNet.Symbolics.LinearAlgebra

open MathNet.Symbolics
open Core
open Utils
open NumberTheory

let formatGeneric (e : obj) =
    match e with
    | :? Expression as ex -> ex.ToFormattedString()
    | _ -> string e

let inline dot a b = List.map2 (*) a b |> List.sum

let dotc a b = List.map2 (fun x (y:Complex) -> x * y.Conjugate) a b |> List.sum

let parts = Array.map (flip (-) 1) [| 2; 3; 3; 2; 3; 1; 1; 3; 1; 2; 2; 1 |]

let inline crossproduct (v1 : _ []) (v2 : _ []) =
    [ for i in 0..4..parts.Length - 4 ->
          v1.[parts.[0 + i]] * v2.[parts.[1 + i]]
          - v1.[parts.[2 + i]] * v2.[parts.[3 + i]] ]

let inline vecmatrixmult (v : _ list) (m : _ list list) =
    [ for r in List.transpose m -> dot v r ]

let inline matrixvecmult (m : _ list list) (v : _ list) =
    [ for r in m -> dot v r ]

let inline matrixmatrixmult (m1 : _ list list) (m2 : _ list list) =
    let m2T = List.transpose m2
    [ for r in m1 ->
          [ for c in m2T -> dot r c ] ]

let vecmatrixmultc (v : _ list) (m : _ list list) =
    [ for r in List.transpose m -> dotc v r ]

let matrixvecmultc (m : _ list list) (v : _ list) =
    [ for r in m -> dotc v r ]

let matrixmatrixmultc (m1 : _ list list) (m2 : _ list list) =
    let m2T = List.transpose m2
    [ for r in m1 ->
          [ for c in m2T -> dotc r c ] ]

let identityM zero one n =
    [ for r in 1..n ->
          [ for c in 1..n ->
                if r = c then one
                else zero ] ]

let removeRow i (m : 'a list list) =
    [ for r in 0..m.Length - 1 do
          if r <> i then yield m.[r] ]

let removeCol i (m : 'a list list) =
    [ for r in 0..m.Length - 1 ->
          [ for c in 0..m.[r].Length - 1 do
                if c <> i then yield m.[r].[c] ] ]

let inline det2 (a : 'a list list) =
    a.[0].[0] * a.[1].[1] - a.[0].[1] * a.[1].[0]

let inline det3 (m : 'a list list) =
    let a = m.[0].[0]
    let b = m.[0].[1]
    let c = m.[0].[2]
    let d = m.[1].[0]
    let e = m.[1].[1]
    let f = m.[1].[2]
    let g = m.[2].[0]
    let h = m.[2].[1]
    let i = m.[2].[2]
    a * e * i + b * f * g + c * d * h - c * e * g - b * d * i - a * f * h

let inline det (m : ^a list list) =
    let rec loop (m : ^a list list) =
        let i = m.Length
        if i = 1 then m.[0].[0]
        elif i = 2 then det2 m
        else
            let m' = removeRow 0 m

            let detf =
                if i = 3 then det2
                else loop
            [ for c in 0..m.[0].Length - 1 ->
                  let var = m.[0].[c]
                  let detm = var * detf (removeCol c m')
                  if c % 2 = 0 then detm
                  else -detm ]
            |> List.sum
    loop m

let inline minor r c (m : ^a list list) =
    let m' = removeRow (r - 1) m |> removeCol (c - 1)
    if (r + c) % 2 = 0 then det m'
    else -(det m')

let inline cofactor (m : _ list) =
    let n = m.Length
    [ for r in 1..n ->
          [ for c in 1..n -> minor r c m ] ]

let inline adjugate l =
    l
    |> cofactor
    |> List.transpose

let inline inverse m =
    let cT = adjugate m
    List.map (List.map ((*) (1Q / (det m)))) cT

type Vector<'a when 'a: equality>(l : 'a list) =
    member __.AsList = l
    member __.Item
        with get (index) = l.[index]
    static member inline (*) (a : Expression, b : Vector<_>) =
        Vector(List.map ((*) a) b.AsList)
    static member inline (*) (a : Complex, b : Vector<_>) =
        Vector(List.map ((*) a) b.AsList)
    static member inline (*) (a : Vector<_>, b : Expression) =
        Vector(List.map ((*) b) a.AsList)
    static member inline (*) (a : Vector<_>, b : Complex) =
        Vector(List.map ((*) b) a.AsList)
    static member inline (*) (a : Vector<_>, b : Vector<_>) =
        dot a.AsList b.AsList
    static member inline (/) (a : Vector<_>, b : Expression) =
        Vector(List.map (fun x -> x/b) a.AsList)
    static member inline (/) (a : Vector<_>, b : Complex) =
        Vector(List.map (fun x -> x/b) a.AsList)
    static member inline (-) (a : Vector<_>, b : Vector<_>) =
        Vector(List.map2 (-) a.AsList b.AsList)
    static member inline (+) (a : Vector<_>, b : Vector<_>) =
        Vector(List.map2 (+) a.AsList b.AsList)
    static member inline (<*>) (a : Vector<_>, b : Vector<_>) =
        Vector(List.map2 (*) a.AsList b.AsList)
    static member (*) (a : Vector<Complex>, b : Vector<Complex>) =
        List.map2 (fun z1 (z2:Complex) -> z1 * z2.Conjugate) a.AsList b.AsList
        |> List.sum
    override t.ToString() =
        let br1, br2 =
            if expressionFormat = "Infix" then "[", "]"
            else "\\left[", "\\right]"
        sprintf "%s%s%s" br1
            (List.map formatGeneric t.AsList |> String.concat ",") br2
    override t.GetHashCode () = hash t.AsList
    override v.Equals(o) =
        match o with
        | :? Vector<'a> as w -> v.AsList = w.AsList
        | _ -> false

module Vector =
    let toList (v : Vector<_>) = v.AsList
    let map f (v : Vector<_>) = Vector(List.map f v.AsList)
    
    let toBasisExpression (bs:List<Expression>, v:Vector<_>) =
        List.map2 (fun el b -> hold el * vec b) v.AsList bs
        |> List.sum
  
    let map2 f (v : Vector<_>) (v2 : Vector<_>) = Vector(List.map2 f v.AsList v2.AsList)
    let inline lpNorm (p : Expression) (v : Vector<_>) =
        (v.AsList |> List.sumBy (fun x -> (abs x) ** p)) ** (1 / p)

    let inline crossproduct (v1 : Vector<_>) (v2 : Vector<_>) =
        if v1.AsList.Length <> 3 && v2.AsList.Length <> 3 then
            failwith "Must be a 3-vector"
        else
            crossproduct (List.toArray v1.AsList) (List.toArray v2.AsList)
            |> Vector

type Matrix<'a>(l : 'a list list) =
    member __.AsList = l
    static member inline (*) (a : Expression, b : Matrix<_>) =
        Matrix(List.map (List.map ((*) a)) b.AsList)
    static member inline (*) (a : Matrix<_>, b : Expression) =
        Matrix(List.map (List.map ((*) b)) a.AsList)
    static member inline (*) (a : Vector<_>, b : Matrix<_>) =
        Vector(vecmatrixmult a.AsList b.AsList)
    static member inline (*) (a : Matrix<_>, b : Vector<_>) =
        Vector(matrixvecmult a.AsList b.AsList)
    static member inline (*) (a : Matrix<_>, b : Matrix<_>) =
        Matrix(matrixmatrixmult a.AsList b.AsList)
    override t.ToString() =
        if Utils.expressionFormat = "Infix" then
            sprintf "\n%s"
                (String.concat "\n"
                     (List.map (List.map formatGeneric >> String.concat ", ")
                          t.AsList))
        else
            sprintf "\\begin{bmatrix}\n%s\n\\end{bmatrix}"
                (String.concat "\\\\ \n"
                     (List.map
                          (List.map (fun v -> sprintf "{%s}" (formatGeneric v))
                           >> String.concat " & ") t.AsList))

module Matrix =
    let toList (m : Matrix<_>) = m.AsList
    let map f (m : Matrix<_>) = Matrix(List.map (List.map f) m.AsList)
    let inline determinant (m : Matrix<_>) = det m.AsList
    let inline inverse (m : Matrix<_>) = Matrix(inverse m.AsList)
    let inline identity n = Matrix(identityM 0Q 1Q n)
    let inline identity2 zero one n = Matrix(identityM zero one n)
    let inline transpose (m:Matrix<_>) = Matrix(List.transpose m.AsList)
    let reshape (r,c) (vs:_ seq) =
        let avs = Seq.toArray vs
        Matrix ([for x in 0..r-1 -> [for y in 0..c-1 -> avs.[x * c + y]]])

