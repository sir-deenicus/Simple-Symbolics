module MathNet.Symbolics.LinearAlgebra

open System.Numerics
open MathNet.Numerics
open MathNet.Symbolics
open Core
open Utils
open NumberProperties
open Prelude.Common
open Prelude.Math
open Prelude 

let formatGeneric (e : obj) =
    match e with
    | :? Expression as ex -> ex.ToFormattedString()
    | _ -> string e


let inline dot a b = Array.map2 (*) a b |> Array.sum

let dotc a b = Array.map2 (fun x (y:Complex) -> x * y.Conjugate) a b |> Array.sum

let inline crossproduct (v1 : _ []) (v2 : _ []) =
    let parts = Array.map (flip (-) 1) [| 2; 3; 3; 2; 3; 1; 1; 3; 1; 2; 2; 1 |]
    [| for i in 0..4..parts.Length - 4 ->
          v1.[parts.[0 + i]] * v2.[parts.[1 + i]]
          - v1.[parts.[2 + i]] * v2.[parts.[3 + i]] |]

let inline vecmatrixmult (v : _ []) (m : _ [] []) =
    [| for r in Array.transpose m -> dot v r |]

let inline matrixvecmult (m : _ [] []) (v : _ []) =
    [| for r in m -> dot v r |]

let inline matrixmatrixmult (m1 : _ [] []) (m2 : _ [] []) =
    let m2T = Array.transpose m2
    [| for r in m1 ->
          [| for c in m2T -> dot r c |] |]

let vecmatrixmultc (v : _ []) (m : _ [] []) =
    [| for r in Array.transpose m -> dotc v r |]

let matrixvecmultc (m : _ [] []) (v : _ []) =
    [| for r in m -> dotc v r |]

let matrixmatrixmultc (m1 : _ [] []) (m2 : _ [] []) =
    let m2T = Array.transpose m2
    [| for r in m1 ->
          [| for c in m2T -> dotc r c |] |]

let identityM zero one n =
    [| for r in 1..n ->
          [| for c in 1..n ->
                if r = c then one
                else zero |] |]

let removeRow i (m : 'a [] []) =
    [| for r in 0..m.Length - 1 do
          if r <> i then yield m.[r] |]

let removeCol i (m : 'a [] []) =
    [| for r in 0..m.Length - 1 ->
          [| for c in 0..m.[r].Length - 1 do
                if c <> i then yield m.[r].[c] |] |]

let inline det2 (a : 'a [] []) =
    a.[0].[0] * a.[1].[1] - a.[0].[1] * a.[1].[0]

let inline det3 (m : 'a [] []) =
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

let inline det (m : ^a [] []) =
    let rec loop (m : ^a [] []) =
        let i = m.Length
        if i = 1 then m.[0].[0]
        elif i = 2 then det2 m
        else
            let m' = removeRow 0 m

            let detf = if i = 3 then det2 else loop

            [| for c in 0..m.[0].Length - 1 ->
                let var = m.[0].[c]
                let detm = var * detf (removeCol c m')
                if c % 2 = 0 then detm else -detm |]
            |> Array.sum
    loop m

let inline minor r c (m : ^a [] []) =
    let m' = removeRow (r - 1) m |> removeCol (c - 1)
    if (r + c) % 2 = 0 then det m'
    else -(det m')

let inline cofactor (m : _ []) =
    let n = m.Length
    [| for r in 1..n ->
        [| for c in 1..n -> minor r c m |] |]

let inline adjugate l =
    l
    |> cofactor
    |> Array.transpose

let inline inverse m =
    let cT = adjugate m
    Array.map (Array.map ((*) (1Q / (det m)))) cT


type VectorFormat =
    | Row
    | Column

let mutable vectorFormat = VectorFormat.Row

type Vector<'a when 'a: equality>(elems : 'a []) =
    //let a = Array.ofList elems
    let mutable format = vectorFormat
    member __.AsList = List.ofArray elems

    member __.AsArray = elems
    member __.Item
        with get (index) = elems.[index]
        and set (index) (value) = elems.[index] <- value

    new (l : 'a list) = 
        Vector(l |> Array.ofList )

    member __.GetSlice(startIdx1:int, endIdx1 : int option) = 
        let endidx1 = defaultArg endIdx1 (elems.Length - 1)
        Vector elems[startIdx1..endidx1]

    member __.GetSlice(startIdx1:int option, endIdx1 : int) = 
        let startidx1 = defaultArg startIdx1 0
        Vector elems[startidx1..endIdx1] 

    member __.GetSlice(startIdx1:int option, endIdx1 : int option) = 
        let startidx1 = defaultArg startIdx1 0
        let endidx1 = defaultArg endIdx1 (elems.Length - 1)
        Vector elems[startidx1..endidx1] 

    member __.GetSlice(startIdx1:int, endIdx1 : int) = 
        Vector elems[startIdx1..endIdx1]
        
    member __.GetReverseIndex(_, offset) =  
        elems.Length - 1 - offset

    member __.Shape = 
        match format with
        | VectorFormat.Row -> (1, elems.Length)
        | VectorFormat.Column -> (elems.Length, 1)

    member __.Length = elems.Length

    member __.InternalFormat with get() = format and set f = format <- f
    
    static member inline (~-) (a : Vector<_>) = Vector (List.map (fun x -> -x) a.AsList)
    
    static member inline (*) (a : Expression, b : Vector<_>) =
        Vector(List.map ((*) a) b.AsList)
    static member inline (*) (a : Vector<_>, b : Expression) =
        Vector(List.map ((*) b) a.AsList)

    static member inline (*) (a : Vector<float>, b : float) =
        Vector(List.map ((*) b) a.AsList) 
    static member inline (*) (a : float, b : Vector<float>) =
        Vector(List.map ((*) a) b.AsList)

    static member inline (*) (a : Vector<Expression>, b : float) =
        Vector(List.map ((*) b) a.AsList) 

    static member inline (*) (a : float, b : Vector<Expression>) =
        Vector(List.map ((*) a) b.AsList)

    static member inline (*) (a : Vector<float32>, b : float32) =
        Vector(List.map ((*) b) a.AsList)
    static member inline (*) (a : float32, b : Vector<float32>) =
        Vector(List.map ((*) a) b.AsList)

    static member inline (*) (a : Vector<Expression>, b : float32) =
        Vector(List.map ((*) b) a.AsList)
    static member inline (*) (a : float32, b : Vector<Expression>) =
        Vector(List.map ((*) a) b.AsList)

    static member inline (*) (a : Vector<int>, b : int) =
        Vector(List.map ((*) b) a.AsList) 
    static member inline (*) (a : int, b : Vector<int>) =
        Vector(List.map ((*) a) b.AsList)

    static member inline (*) (a : int, b : Vector<Units.Units>) =
        Vector(List.map ((*) a) b.AsList) 
    static member inline (*) (a : Vector<Units.Units>, b : int) =
        Vector(List.map ((*) b) a.AsList) 
    static member inline (*) (a : Vector<_>, b : Units.Units) =
        Vector(List.map ((*) b) a.AsList)

    static member inline (*) (a : Complex, b : Vector<_>) =
        Vector(List.map ((*) a) b.AsList)
    static member inline (*) (a : Vector<_>, b : Complex) =
        Vector(List.map ((*) b) a.AsList)
  
    static member inline (*) (a : Vector<_>, b : Vector<_>) =
        dot a.AsArray b.AsArray
        
    static member inline (/) (a : Vector<_>, b : Expression) =
        Vector(List.map (fun x -> x/b) a.AsList)

    static member inline (/) (a : Expression, b : Vector<_>) =
        Vector(List.map (fun x -> a/x) b.AsList)

    static member inline (/) (a : Vector<Expression>, b : float) =
        Vector(List.map (fun x -> x/b) a.AsList)

    static member inline (/) (a : Vector<float32>, b : float32) =
        Vector(List.map (fun x -> x/b) a.AsList)
    
    static member inline (/) (a : Vector<float>, b : float) =
        Vector(List.map (fun x -> x/b) a.AsList)
    
    static member inline (/) (a : Vector<_>, b : Complex) =
        Vector(List.map (fun x -> x/b) a.AsList)

    static member (/) (a : Vector<Units.Units>, b : Units.Units) =
        Vector(List.map (fun x -> x/b) a.AsList)

    static member inline (/) (a : Vector<_>, b : Vector<_>) = 
        Vector(List.map2 (/) a.AsList b.AsList)
        
    static member inline (-) (a : Vector<_>, b : Vector<_>) =
        Vector(List.map2 (-) a.AsList b.AsList)
        
    static member inline (+) (a : Vector<_>, b : Vector<_>) =
        Vector(List.map2 (+) a.AsList b.AsList)

    static member inline (+) (a : Vector<_>, b : Expression) =
        Vector(Array.map (fun x -> x + b) a.AsArray)

    static member inline (+) (a : Vector<float>, b : float) =
        Vector(Array.map (fun x -> x + b) a.AsArray)

    static member inline (+) (a : Vector<float32>, b : float32) =
        Vector(Array.map (fun x -> x + b) a.AsArray)
        
    static member inline (<*>) (a : Vector<_>, b : Vector<_>) =
        Vector(List.map2 (*) a.AsList b.AsList)  
    
    member __.dot(a : Vector<Complex>, b : Vector<Complex>) =
        List.map2 (fun z1 (z2:Complex) -> z1 * z2.Conjugate) a.AsList b.AsList
        |> List.sum 

    member inline __.dot(a : Vector<_>, b : Vector<_>) = dot a.AsArray b.AsArray
      
    member v.formatAsColumnVector () =
        if Utils.expressionFormat = "Infix" then
            sprintf "\n%s"
                (String.concat "\n"
                    (List.map (fun s -> "[" + formatGeneric s + "]") v.AsList ))
        else
            sprintf "\\begin{bmatrix}\n%s\n\\end{bmatrix}"
                (String.concat "\\\\ \n"
                    (List.map (fun v -> sprintf "%s" (formatGeneric v)) v.AsList))

    member v.ToScalar() =
        if v.Length = 1 then v[0]
        else failwith "Vector is not a scalar"

    override t.ToString() =
        match format with
        | Column -> t.formatAsColumnVector()
        | Row ->
            let br1, br2 =
                if expressionFormat = "Infix" then "[", "]"
                else "\\left[", "\\right]"
            sprintf "%s%s%s" br1
                (List.map formatGeneric t.AsList |> String.concat ",") br2

    override t.GetHashCode () = t.AsList.GetHashCode()
    
    override v.Equals(o) =
        match o with
        | :? Vector<'a> as w -> v.AsList = w.AsList
        | _ -> false

    interface System.Collections.IEnumerable with
        member v.GetEnumerator() = 
            (v.AsList :> seq<_>).GetEnumerator()
              
    interface System.Collections.Generic.IEnumerable<'a> with
        member v.GetEnumerator() = 
            (v.AsList :> seq<'a>).GetEnumerator()
         
     
module BroadcastHelper =
    let broadcastOp1 op (opvec : Vector<_> -> Vector<_> -> Vector<_>) (a : 'a [] [], b : Vector<_>) =
        //dont use map all lengths are equal
        let columnsLen = a[0].Length
        let rowsLen = a.Length
        //broadcasting is done by repeating the vector for each row or column
        //depending on the shape of the matrix and vector respectively        
        if columnsLen = b.Length then
            //subtract each row of the matrix by the vector
            a |> Array.map (fun r -> opvec (Vector r) b) 
        elif rowsLen = b.Length then
            //subtract each column of the matrix by the vector
            a 
            |> Array.transpose 
            |> Array.map (fun r -> (opvec (Vector r) b).AsArray) 
            |> Array.transpose 
            |> Array.map Vector

        elif b.Length = 1 then
            //subtract each row of the matrix by the vector
            a |> Array.map (fun r -> Array.map (fun x -> op x b.[0]) r |> Vector)  
        else
            failwith "Matrix and vector must have compatible shapes"

    let broadcastOp2 op (opvec : Vector<_> -> Vector<_> -> Vector<_>) (a : Vector<_>, b : 'a [] []) =
        //dont use map all lengths are equal
        let columnsLen = b[0].Length
        let rowsLen = b.Length
        //broadcasting is done by repeating the vector for each row or column
        //depending on the shape of the matrix and vector respectively        
        if columnsLen = a.Length then
            //subtract each row of the matrix by the vector
            b |> Array.map (fun r -> opvec a (Vector r)) 
        elif rowsLen = a.Length then
            //subtract each column of the matrix by the vector
            b 
            |> Array.transpose 
            |> Array.map (fun r -> (opvec a (Vector r)).AsArray) 
            |> Array.transpose 
            |> Array.map Vector

        elif a.Length = 1 then
            //subtract each row of the matrix by the vector
            b |> Array.map (fun r -> Array.map (fun x -> op a.[0] x) r |> Vector)  
        else
            failwith "Matrix and vector must have compatible shapes"

type Matrix<'a when 'a: equality>(elems : 'a [] []) = 
    new(vs : Vector<'a> list) = Matrix([|for r in vs -> r.AsArray|])

    new(vs: Vector<'a> []) = Matrix(vs |> Array.map (fun v -> v.AsArray))

    new(vs : 'a list list) = Matrix([|for r in vs -> List.toArray r|])
    member __.AsArray = elems

    member __.AsList = elems |> Array.map Array.toList |> Array.toList

    member __.T = Matrix(Array.transpose elems)
    member __.Item
        with get (index1, index2) = elems.[index1].[index2]
        and set (index1, index2) value = elems.[index1].[index2] <- value

    member __.GetSlice(startIdx1:int option, endIdx1 : int option, idx2:int) =
        let sidx1 = defaultArg startIdx1 0
        let endidx1 = defaultArg endIdx1 (elems.Length - 1)
        Vector [for r in elems.[sidx1..endidx1] -> r.[idx2]]

    member __.GetSlice(idx1:int,startIdx2:int option, endIdx2 : int option) =
        let sidx2 = defaultArg startIdx2 0
        let endidx2 = defaultArg endIdx2 (elems.[idx1].Length - 1)
        Vector elems.[idx1].[sidx2..endidx2]

    member __.GetSlice(startIdx1:int option, endIdx1 : int option,startIdx2:int option, endIdx2 : int option) =
        let sidx1 = defaultArg startIdx1 0
        let sidx2 = defaultArg startIdx2 0
        let endidx1 = defaultArg endIdx1 (elems.Length - 1)
        let endidx2 = defaultArg endIdx2 (elems.[sidx1].Length - 1)
        Matrix [|for r in elems.[sidx1..endidx1] -> r.[sidx2..endidx2]|] 
         
    member m.GetReverseIndex(i, offset) =  
       m.Dims[i] - 1 - offset
       
    member __.shape = elems.Length, elems.[0].Length
    
    member __.Dims : int[] = [|elems.Length; elems.[0].Length|]

    member m.RowsLen = fst m.shape

    member m.ColumnsLen = snd m.shape
    
    member m.ToScalar() = 
        if m.RowsLen = 1 && m.ColumnsLen = 1 then
            m.[0,0]
        else
            failwith "Matrix must be a scalar"

    member m.ToVector() =
        if m.RowsLen = 1 then
            m[0, *]
        elif m.ColumnsLen = 1 then
            m[*, 0]
        else
            failwith "Matrix must be a vector"
    
    static member inline (<*>) (a : Matrix<_>, b : Matrix<_>) =
        Matrix (Array.map2 (Array.map2 (*)) a.AsArray b.AsArray)

    static member inline (<*>) (a : Matrix<_>, b : Vector<_>) =
        BroadcastHelper.broadcastOp1 (*) (<*>) (a.AsArray, b)
        |> Matrix

    static member inline (<*>) (a : Vector<_>, b : Matrix<_>) =
        BroadcastHelper.broadcastOp2 (*) (<*>) (a, b.AsArray)
        |> Matrix
        
    static member inline (-) (a : Matrix<_>, b : Matrix<_>) =
        Matrix (Array.map2 (Array.map2 (-)) a.AsArray b.AsArray)

    static member inline (-) (a : Matrix<_>, b : Expression) =
        Matrix (Array.map (Array.map (fun x -> x - b)) a.AsArray)

    static member inline (-) (a : Expression, b : Matrix<_>) =
        Matrix (Array.map (Array.map (fun x -> a - x)) b.AsArray)

    static member inline (-) (a : Matrix<_>, b : Vector<_>) =
        BroadcastHelper.broadcastOp1 (-) (-) (a.AsArray, b)
        |> Matrix

    static member inline (-) (a : Vector<_>, b : Matrix<_>) =
        BroadcastHelper.broadcastOp2 (-) (-) (a, b.AsArray)
        |> Matrix

    static member inline (+) (a : Expression, b : Matrix<_>) =
        Matrix (Array.map (Array.map ((+) a)) b.AsArray)
        
    static member inline (+) (a : Matrix<_>, b : Matrix<_>) =
        Matrix (Array.map2 (Array.map2 (+)) a.AsArray b.AsArray)

    static member inline (+) (a : Matrix<_>, b : Expression) =
        Matrix (Array.map (Array.map ((+) b)) a.AsArray)

    static member inline (+) (a : Matrix<_>, b : Vector<_>) =
        BroadcastHelper.broadcastOp1 (+) (+) (a.AsArray, b)
        |> Matrix

    static member inline (+) (a : Vector<_>, b : Matrix<_>) =
        BroadcastHelper.broadcastOp2 (+) (+) (a, b.AsArray)
        |> Matrix

    static member inline (/) (a : Expression, b : Matrix<_>) =
        Matrix (Array.map (Array.map (fun x -> a / x)) b.AsArray)

    static member inline (/) (a : Matrix<_>, b : Expression) =
        Matrix (Array.map (Array.map (fun x -> x / b)) a.AsArray) 


    static member inline (/) (a : Matrix<_>, b : Vector<_>) = 
        BroadcastHelper.broadcastOp1 (/) (/) (a.AsArray, b)
        |> Matrix

    static member inline (*) (a : int, b : Matrix<int>) =
        Matrix(Array.map (Array.map ((*) a)) b.AsArray)    
    static member inline (*) (a : Expression, b : Matrix<_>) =
        Matrix(Array.map (Array.map ((*) a)) b.AsArray)
    static member inline (*) (a : Matrix<_>, b : Expression) =
        Matrix(Array.map (Array.map ((*) b)) a.AsArray)
    static member inline (*) (a : Vector<_>, b : Matrix<_>) =
        Vector(vecmatrixmult a.AsArray b.AsArray)
    static member inline (*) (a : Matrix<_>, b : Vector<_>) =
        Vector(matrixvecmult a.AsArray b.AsArray)
    static member inline (*) (a : Matrix<_>, b : Matrix<_>) =
        Matrix(matrixmatrixmult a.AsArray b.AsArray)

    //equality
    override m.GetHashCode() =
        m.AsArray.GetHashCode()

    override m.Equals(obj) =
        match obj with
        | :? Matrix<'a> as m2 -> m.AsArray = m2.AsArray
        | _ -> false
        
    override t.ToString() =
        if Utils.expressionFormat = "Infix" then
            sprintf "\n%s"
                (String.concat "\n"
                     (Array.map (Array.map formatGeneric >> String.concat ", " >> fun s -> "["+s+"]")
                          t.AsArray))
        else
            sprintf "\\begin{bmatrix}\n%s\n\\end{bmatrix}"
                (String.concat "\\\\ \n"
                     (Array.map
                          (Array.map (fun v -> sprintf "{%s}" (formatGeneric v))
                           >> String.concat " & ") t.AsArray))

module Generic =
    module Vector =
        let inline magnitude (v:Vector<_>) =
            v.AsArray |> Array.sumBy squared |> sqrt 

        let map f (v : Vector<_>) = 
            let v' = Vector(List.map f v.AsList)
            v'.InternalFormat <- v.InternalFormat
            v'

        let reduce f (v : Vector<_>) = List.reduce f v.AsList

        ///zero vector of dim n
        let zero zeroElem n = Vector (List.replicate n zeroElem)

        let ones oneElem n = Vector (List.replicate n oneElem)

        let inline sum v = reduce (+) v

        let inline mean ofInt (v:Vector<_>) = 
            let n = ofInt v.Length 
            sum v / n

        let inline variance ofInt (v:Vector<_>) =  
            let n = ofInt v.Length  
            let m = mean ofInt v
            sum (map (fun x -> (x - m) ** ofInt 2) v) / n 

    module Matrix = 
        let zero zeroElem (r,c) = Matrix [| for i in 1..r -> Vector.zero zeroElem c |]

        let ones oneElem (r,c) = Matrix [| for i in 1..r -> Vector.ones oneElem c |]

module Vector =
    let toList (v : Vector<_>) = v.AsList
     
    let head (v:Vector<_>) = List.head v.AsList
    
    let map f (v : Vector<_>) = 
        let v' = Vector(List.map f v.AsList)
        v'.InternalFormat <- v.InternalFormat
        v'

    let mapi f (v : Vector<_>) = 
        let v' = Vector(List.mapi f v.AsList)
        v'.InternalFormat <- v.InternalFormat
        v'

    let reduce f (v : Vector<_>) = List.reduce f v.AsList

    let inline sum v = reduce (+) v

    let inline normalize (v : Vector<_>) =  v / sum v

    let replaceSymbols vars = map (replaceSymbols vars)

    let toBasisExpression (bs:List<Expression>, v:Vector<_>) =
        List.map2 (fun el b -> hold el * vec b) v.AsList bs
        |> List.sum

    let map2 f (v : Vector<_>) (v2 : Vector<_>) = Vector(List.map2 f v.AsList v2.AsList)

    let linspace (start : Expression) (stop : Expression) (n : int) =
        let step = (stop - start) / (n - 1)
        Vector [for i in 0..n-1 -> start + step * i]

    let inline lpNorm (p : Expression) (v : Vector<Expression>) =
        (v.AsArray |> Array.sumBy (fun x -> (abs x) ** p)) ** (1 / p) 
        |> Expression.simplify
         
    let inline magnitude (v: Vector<'a>) = 
        sqrtf (v |> map squared |> sum)
     
    let inline toUnit (v: Vector<'a>) = 
        let norm = magnitude v
        v / norm

    let inline norm (v:Vector<_>) = magnitude v

    let cosineSimilarity (v:Vector<Expression>) (v2 : Vector<Expression>) =
        (v * v2) / ((sqrt (v * v)) * (sqrt (v2 * v2)))

    let inline softmax (v:Vector<_>) =
        let v' = map exp v
        v' |> map (fun x -> x / (v' |> reduce (+)))
        
    let toRowMatrix(v:Vector<_>) =
        Matrix [v.AsList]

    let toColumnMatrix (v:Vector<_>) =
        Matrix (List.map List.singleton v.AsList)

    let inline crossproduct (v1 : Vector<_>) (v2 : Vector<_>) =
        if v1.AsList.Length <> 3 && v2.AsList.Length <> 3 then
            failwith "Must be a 3-vector"
        else
            crossproduct (List.toArray v1.AsList) (List.toArray v2.AsList)
            |> Vector 
         
    ///generate random vector 
    let random n = Vector [for _ in 0..n-1 -> random.NextDouble() |> ofFloat] 

    let randn n = Vector [for _ in 0..n-1 -> MathNet.Numerics.Distributions.Normal.Sample(0.0, 1.0) |> ofFloat]

    let toTupled (v:Vector<_>) = Tupled v.AsList
     
    let mean (v:Vector<Expression>) = Generic.Vector.mean Expression.FromInt32 v

    let variance (v:Vector<Expression>) = Generic.Vector.variance Expression.FromInt32 v

    let ones d = Vector [ for i in 1..d -> 1Q ]

    let zeros d = Vector [ for i in 1..d -> 0Q ]

    let onesLike (v:Vector<_>) = ones v.Length

    let zerosLike (v:Vector<_>) = zeros v.Length

    let toScalar (v:Vector<_>) = v.AsList |> List.head

    let inline ofScalar (s:'a) = Vector [s]

module Matrix =
    open MathNet.Numerics.Distributions

    let toList (m : Matrix<_>) = m.AsArray
    
    let inline transpose (m:Matrix<_>) = Matrix(Array.transpose m.AsArray)

    let map f (m : Matrix<_>) = Matrix(Array.map (Array.map f) m.AsArray)

    let mapi f (m : Matrix<_>) = Matrix(Array.mapi (fun i v -> Array.mapi (fun j v' -> f i j v') v) m.AsArray)

    let mapiRows f (m : Matrix<_>) = 
        let r' : 'b Vector [] = m.[..m.RowsLen - 1, *].AsArray |> Array.mapi (fun i v -> f i (Vector v)) 
        Matrix r'

    let mapRows f (m : Matrix<_>) = 
        let r' : 'b Vector [] = m.[..m.RowsLen - 1, *].AsArray |> Array.map (Vector >> f) 
        Matrix(r')

    let inline softmax (m:Matrix<_>) =
        //softmax on a matrix is the softmax on each row
        mapRows Vector.softmax m
    
    let ofVectorRows(vs : seq<Vector<_>>) =
        [for v in vs -> v.AsList] |> Matrix

    let ofVectorCols(vs : seq<Vector<_>>) =
        [for v in vs -> v.AsList] |> Matrix |> transpose

    let toVector (m:Matrix<_>) = Vector (Array.concat m.AsArray)

    let toScalar (m:Matrix<_>) = 
        if m.RowsLen = 1 && m.ColumnsLen = 1 then
            m.[0,0]
        else
            failwith "Matrix must be 1x1"

    let mapCols f (m:Matrix<_>) =
        m |> transpose |> mapRows f |> transpose

    let inline sum (m:Matrix<_>) =
        m.AsArray |> Array.sumBy Array.sum

    let ones (r:int, c:int) = Matrix [ for i in 1..r -> Vector.ones c ]

    let zeros (r:int, c:int) = Matrix [ for i in 1..r -> Vector.zeros c ]
        
    let inline determinant (m : Matrix<_>) = det m.AsArray
    let inline inverse (m : Matrix<_>) = Matrix(inverse m.AsArray)
    let inline identity n = Matrix(identityM 0Q 1Q n)
    let inline identity2 zero one n = Matrix(identityM zero one n)

    let inline LU_decomposition (zero,one) (m : Matrix<_>) =
        let M = array2D m.AsArray
        let U = Array2D.map id M
        let L = array2D (identityM zero one M.RowCount)
        let n = M.RowCount
        for k in 0..n-2 do
            for j in k+1..n-1 do
                L.[j,k] <- U.[j,k] / U.[k,k]
                let ljk = L.[j,k]
                for r in k..n-1 do
                    U.[j,r] <- U.[j,r] - ljk * U.[k, r]
        L, U

    let reshape (r,c) (vs:_ seq) =
        let avs = Seq.toArray vs
        Matrix ([for x in 0..r-1 -> [for y in 0..c-1 -> avs.[x * c + y]]])
         

    let ofVarsEx letter (start1, stop1) (start2, stop2) =
        [for i in start1..stop1 do
            for j in start2..stop2 ->
                subs (Vars.ofChar letter) [(ofInteger i); ofInteger j] ]
        |> reshape (stop1 - start1 + 1, stop2 - start2 + 1)
          

    let zerosLike (m:Matrix<_>) = Generic.Matrix.zero 0Q (m.RowsLen, m.ColumnsLen)

    let onesLike (m:Matrix<_>) = Generic.Matrix.ones 1Q (m.RowsLen, m.ColumnsLen) 
    
    //generate random matrix
    let random (r,c) = [for _ in 0..c-1 do for _ in 0..r-1 -> random.NextDouble() |> ofFloat] |> reshape (r,c)

    let rand (r,c) = random (r,c)
    
    let randomNormal (r,c) = [for _ in 0..c-1 do for _ in 0..r-1 -> Normal(0.0, 1.0).Sample() |> ofFloat] |> reshape (r,c)

    let randn (r,c) = randomNormal (r,c)

    let randomSquareNormal n = randomNormal (n,n)

    let randnSq n = randomSquareNormal n
         
    //generate random square matrix
    let randomSquare n = [for _ in 0..n-1 do for _ in 0..n-1 -> Math.random.NextDouble() |> ofFloat] |> reshape (n,n)
     
    let inline getColumns (m:Matrix<_>) = [for i in 0..m.ColumnsLen - 1 -> m.[*, i]]
    
    let inline getRows (m:Matrix<_>) = [for i in 0..m.RowsLen - 1 -> m.[i, *]]
    
    let stack (ms:Matrix<_> list) =
        ms |> List.map getRows |> List.concat |> Matrix
    
    let inline kroneckerProductView (m1:Matrix<_>) (m2:Matrix<_>) =
        map ((*) m2) m1

    let hAppend (m1:Matrix<_>) (m2:Matrix<_>) =
        Matrix (mergeTwoListOfLists m1.AsList m2.AsList)

    let inline kroneckerProduct (m1:Matrix<'a>) (m2:Matrix<'b>) =
        m1 
        |> map ((*) m2)
        |> getRows 
        |> List.map (Vector.reduce hAppend)  
        |> stack

    let inline kroneckerProductB (m1:Matrix<_>) (m2:Matrix<_>) =
        let cols = m1.ColumnsLen * m2.ColumnsLen
        let rows = m1.RowsLen * m2.RowsLen
        [ for r in 0 .. m1.RowsLen - 1 do
            for r2 in 0 .. m2.RowsLen - 1 do
                for c in 0 .. m1.ColumnsLen - 1 do
                    for c2 in 0 .. m2.ColumnsLen - 1 do
                        m1[r, c] * m2[r2, c2] ]
            |> reshape (rows, cols)  

    //extract hadamard product from c
            
    let diagonal (m:Matrix<_>) =
        if m.RowsLen <> m.ColumnsLen then
            failwith "Matrix must be square" 
        Vector [ for i in 0 .. m.RowsLen - 1 -> m.[i,i] ]
        

    let inline trace (m:Matrix<_>) = diagonal m |> Vector.sum  

    ///extract hadamard product matrix from kronecker product matrix
    let extractHadamardFromKronecker (sourceRowsLen, sourceColumnsLen) (m:Matrix<Expression>) =
        //To select the hadamard product, we need to enter into each submatrix 
        //and then the respective position in the submatrix
        [ for r in 0..sourceRowsLen - 1 do
            for c in 0..sourceColumnsLen - 1 do
                let innerCol = c * sourceColumnsLen + c
                let innerRow = r * sourceRowsLen + r
                m[innerRow, innerCol]]
        |> reshape(sourceRowsLen, sourceColumnsLen)

    let randomPermutationMatrix n =
        let takenIndices = Array.create n false

        [ for i in 0 .. n - 1 do
              let v = Vector.zeros n

              let indices =
                  takenIndices
                  |> Array.mapi (fun i b -> if b then None else Some i)
                  |> Array.choose id

              let index = Array.sampleOne indices
              takenIndices[index] <- true
              v[index] <- 1Q
              v ]
        |> ofVectorRows

    let split (n: int) (m: Matrix<_>) =
        let cols = m.ColumnsLen
        let parts = cols / n
        let remainder = cols % n

        if remainder <> 0 then
            failwith $"Cannot split matrix into {n} parts because {cols} is not divisible by {n}"
        //next we need to split the matrix into n parts along the columns
        [ for i in 0..parts .. cols - 1 do
              if i + parts <= cols then
                  m.[*, i .. i + parts - 1] ]
         
let vector (v:_ list) = Vector v

[<AutoOpen>]
module MatrixExtensions =
    
    open System.Collections.Generic

    type Vector<'a when 'a: equality> with 
        static member ofVars(letter, n, ?start) =
            let start = defaultArg start 1
            [for i in start..start+(n-1) -> subs (Vars.ofChar letter) [ofInteger i] ]
            |> Vector
        
        static member toLookUpTable (varname, v:Vector<_>,?offset) =
            let offset = defaultArg offset 1
            [ for i in 0..v.Length - 1 -> varname + $"_{{{i+offset}}}", v.[i] ]

    type Matrix<'a when 'a: equality> with

        static member toLookUpTable (varname, m:Matrix<_>,?offset1,?offset2) =
            let offset1, offset2 = defaultArg offset1 1, defaultArg offset2 1 
            [ for j in 0..m.ColumnsLen - 1 do 
                for i in 0..m.RowsLen - 1 -> varname + $"_{{{i+offset1},{j+offset2}}}", m.[i,j]] 

        static member ofVars(letter, width, height,?start) =
            let start = defaultArg start 1
            [for r in start..start+(width-1)do
                for c in start..start+(height-1) ->
                    subs (Vars.ofChar letter) [(ofInteger r); ofInteger c] ]
            |> Matrix.reshape (width, height)

        static member mean (m:Matrix<_>, ?axis) =
            let axis = defaultArg axis -1
            //axis = 0 means mean of each column, axis = 1 means mean of each row
            match axis with
            | 0 -> m |> Matrix.mapCols (Vector.mean >> Vector.ofScalar)
            | 1 -> m |> Matrix.mapRows (Vector.mean >> Vector.ofScalar)
            | _ -> 
                let sum = Matrix.sum m 
                let n = m.RowsLen * m.ColumnsLen
                Matrix [ [sum / n] ]

        static member variance (m:Matrix<_>, ?axis) =
            let axis = defaultArg axis -1
            //axis = 0 means variance of each column, axis = 1 means variance of each row
            match axis with
            | 0 -> m |> Matrix.mapCols (Vector.variance >> Vector.ofScalar)
            | 1 -> m |> Matrix.mapRows (Vector.variance >> Vector.ofScalar)
            | _ -> 
                let mean = Matrix.mean m |> Matrix.toScalar
                let n = m.RowsLen * m.ColumnsLen
                let sumOfSquares = m |> Matrix.map (fun x -> (x - mean) ** 2Q) |> Matrix.sum
                Matrix [ [sumOfSquares / n] ]
            
    /// <summary>
    /// A matrix type that tracks the variables used to construct it. 
    /// The TrackedSymbolicMatrix class is designed to generate a matrix of variables, with each entry being an indexed subscript of the current variable.
    /// </summary>
    /// <param name="chars">The list of characters used to generate the matrix. If None, list of variables starts from 'a' to 'z'.</param>
    /// <param name="startchar">The character to start with for the next variable, If None, variable starts from 'a'. chars` argument overrides this.</param>
    type TrackedSymbolicMatrix(?chars: char list, ?startchar) =
        let chars =
            match chars with
            | Some chars -> Stack (List.rev chars)
            | None ->
                match startchar with
                | Some startchar -> Stack (List.rev [ startchar .. 'z' ])
                | None -> Stack (List.rev [ 'a' .. 'z' ]) 

        /// <summary>
        /// Generates a new matrix of variables based on the current state of the tracked symbolic matrix then advances the currently selected variable.
        /// </summary>
        /// <param name="r">The number of rows in the generated matrix.</param>
        /// <param name="cols">The number of columns in the generated matrix.</param>
        /// <returns>A new matrix of variables.</returns>
        member __.Next(r, cols) = Matrix.ofVars (chars.Pop(), r, cols)         

open System

type Tensor<'a when 'a: equality>(dims, ?storage) =
    let storage = defaultArg storage (Array.zeroCreate (Array.reduce (*) dims))

    member __.Dims = dims 
    member __.Storage = storage
    member __.Length = storage.Length 
    member __.Rank = dims.Length

    //member x.Item 
    //    with get(indices) = 
    //        let index = Array.fold2 (fun acc dim index -> acc + index * dim) 0 dims indices
    //        storage.[index]
    //    and set(indices, value) =
    //        let index = Array.fold2 (fun acc dim index -> acc + index * dim) 0 dims indices
    //        storage.[index] <- value
  
    // member x.einsum (pattern:string, [<ParamArray>] args:Tensor<_> []) =
    //     let pattern = pattern.Split("->")
    //     let inputPattern = pattern.[0].Split(",")
    //     let outputPattern = pattern.[1].Split(",") 

    //     //check args
    //     if inputPattern.Length <> args.Length then
    //         failwith "Number of input patterns must match the number of input tensors"
        
    //     let inputDims = [for i in 0..args.Length - 1 -> args.[i].Dims]
    //     let outputDims = [for i in 0..outputPattern.Length - 1 -> args.[i].Dims] 
   
    static member (+) (a:Tensor<_>, b:Tensor<_>) = 
        if a.Length <> b.Length then
            failwith "Tensors must have the same length"
        let storage = Array.map2 (+) a.Storage b.Storage
        Tensor(a.Dims, storage)

    static member (-) (a:Tensor<_>, b:Tensor<_>) =
        if a.Length <> b.Length then
            failwith "Tensors must have the same length"
        let storage = Array.map2 (-) a.Storage b.Storage
        Tensor(a.Dims, storage)

    //scalar multiplication
    static member (*) (a:Expression, b:Tensor<_>) =
        let storage = Array.map (fun x -> a * x) b.Storage
        Tensor(b.Dims, storage)

    static member (*) (a:Tensor<_>, b:Expression) =
        let storage = Array.map (fun x -> x * b) a.Storage
        Tensor(a.Dims, storage)


module Float =
    module Vector =
        let randn n = Vector [for _ in 0..n-1 -> MathNet.Numerics.Distributions.Normal.Sample(0.0, 1.0)]

        let random n = Vector [for _ in 0..n-1 -> random.NextDouble() ] 
          
        let mean v = Generic.Vector.mean float v
            
        let variance v = Generic.Vector.variance float v

        let ones d = Vector [ for i in 1..d -> 1. ]

        let zeros d = Vector [ for i in 1..d -> 0. ]

        let onesLike (v:Vector<_>) = ones v.Length

        let zerosLike (v:Vector<_>) = zeros v.Length

        let magnitude (v:Vector<float>) = Generic.Vector.magnitude v

module Float32 = 
    module Vector =
        let randn n = Vector [for _ in 0..n-1 -> MathNet.Numerics.Distributions.Normal.Sample(0.0, 1.0) |> float32] 

        let random n = Vector [for _ in 0..n-1 -> random.NextDouble() |> float32 ] 
          
        let mean v = Generic.Vector.mean float32 v
            
        let variance v = Generic.Vector.variance float32 v

        let ones d = Vector [ for i in 1..d -> 1f ]

        let zeros d = Vector [ for i in 1..d -> 0f ]

        let onesLike (v:Vector<_>) = ones v.Length

        let zerosLike (v:Vector<_>) = zeros v.Length

        let magnitude (v:Vector<float32>) = Generic.Vector.magnitude v
         