module MathNet.Symbolics.Core

open MathNet.Symbolics
open MathNet.Numerics
open System
open MathNet.Symbolics.Utils
open Prelude.Common
open MathNet.Symbolics.NumberProperties
open Utils.Func

let ln = Operators.ln
let arctan = Operators.arctan
let sec = Operators.sec
let secant = Operators.sec

let symbol = Operators.symbol
let V = symbol
let (!) (str:string) = symbol(str)
  
module Desc =
    let power = symbol "power"
    let energy = symbol "energy"
    let force = symbol "force"
    let energyflux = symbol "energyflux"
    let volume = symbol "volume"
    let velocity = symbol "velocity"
    let accel = symbol "accel"
    let time = symbol "time"
    let mass = symbol "mass"
    let length = symbol "length"
    let temperature = symbol "temperature"
    let current = symbol "current"
    let currency = symbol "currency"
    let charge = symbol "charge"
    let naira =  symbol "naira"
    let bpound = symbol "gbp"
    let dollar = symbol "dollar"
    let density = symbol "density"

    let Names =
        set
            [   "power"
                "energy"
                "force"
                "energyflux"
                "volume"
                "velocity"
                "accel"
                "time"
                "mass"
                "length"
                "temperature"
                "current" ]

module Vars =
    let a = symbol "a"
    let b = symbol "b"
    let c = symbol "c"
    let d = symbol "d"
    let e = symbol "e"
    let f = symbol "f"
    let g = symbol "g"
    let h = symbol "h"
    let i = symbol "i"
    let j = symbol "j"
    let k = symbol "k"
    let l = symbol "l"
    let m = symbol "m"
    let n = symbol "n"
    let o = symbol "o"
    let p = symbol "p"
    let q = symbol "q"
    let r = symbol "r"
    let s = symbol "s"
    let t = symbol "t"
    let u = symbol "u"
    let v = symbol "v"
    let w = symbol "w"
    let x = symbol "x"
    let y = symbol "y"
    let z = symbol "z"
    let t0 = symbol "t_0"
    let t1 = symbol "t_1"
    let t2 = symbol "t_2"
    let x0 = symbol "x_0"
    let x1 = symbol "x_1"
    let x2 = symbol "x_2"
    let x3 = symbol "x_3"
    let v0 = symbol "v_0"
    let y0 = symbol "y_0"
    let y1 = symbol "y_1"
    let y2 = symbol "y_2"

    let A = V"A"
    let B = V"B"
    let C = V "C"
    let D = V"D"
    let E = V"E"
    let F = V"F"
    let G = V"G"
    let H = V"H"
    let I = V"I"
    let J = V "J"
    let K = V "K"
    let L = V "L"
    let M = V "M"
    let N = V "N"
    let O = V "O"
    let P = V "P"
    let Q = V "Q"
    let R = V"R"
    let S = V"S"
    let T = V "T"
    let U = V"U"
    let W = V"W"
    let X = V"X"
    let Y = V"Y"
    let Z = V"Z"

    let Pi = Constants.pi

    let ofChar (c:char) = symbol (string c)

type Vars() =
    //Α α, Β β, Γ γ, Δ δ, Ε ε, Ζ ζ, Η η, Θ θ, Ι ι, Κ κ, Λ λ, Μ μ, Ν ν, Ξ ξ, Ο ο, Π π, Ρ ρ,  σ,Ω ω.
    static member internal letter greek latex =
        match expressionFormat with
        | InfixFormat -> greek
        | _ -> latex
    static member D = V"D"
    static member V = V"V"
    static member alpha = Vars.letter "α" "\\alpha" |> V
    static member beta = Vars.letter "β" "\\beta" |> V
    static member gamma = Vars.letter "γ" "\\gamma" |> V
    static member Gamma = Vars.letter "Γ" "\\Gamma" |> V
    static member delta = Vars.letter "δ" "\\delta" |> V
    static member Delta = Vars.letter "Δ" "\\Delta"  |> V
    static member epsilon = Vars.letter "ϵ" "\\epsilon" |> V
    static member vepsilon = Vars.letter "ε" "\\varepsilon" |> V
    static member zeta = Vars.letter "ζ" "\\zeta" |> V 
    static member eta = Vars.letter "η" "\\eta" |> V
    static member phi = Vars.letter "ϕ" "\\phi" |> V
    //curly phi
    static member vphi = Vars.letter "φ" "\\varphi" |> V
    static member Phi = Vars.letter "Φ" "\\Phi" |> V
    static member iota = Vars.letter "ι" "\\iota" |> V
    static member Lambda = Vars.letter "Λ" "\\Lambda" |> V
    static member lambda = Vars.letter "λ" "\\lambda" |> V
    static member mu = Vars.letter "μ" "\\mu" |> V
    static member nu = Vars.letter "v" "\\nu" |> V
    static member xi = Vars.letter "ξ" "\\xi" |> V
    static member Xi = Vars.letter "Ξ" "\\Xi" |> V
    static member psi = Vars.letter "ψ" "\\psi" |> V
    static member Theta = Vars.letter "Θ" "\\Theta" |> V
    static member theta = Vars.letter "θ" "\\theta" |> V
    static member rho = Vars.letter "ρ" "\\rho" |> V
    static member sigma = Vars.letter "σ" "\\sigma" |> V
    static member omega = Vars.letter "ω" "\\omega" |> V
    static member Omega = Vars.letter "Ω" "\\Omega" |> V

//==========================================

let mkSymbolMap l = l |> List.map (fun s -> s, symbol s) |> Map

let symbolString =
    function
    | Identifier(Symbol s) -> s
    | _ -> ""

let rec replaceSymbolAux doall r x f =
    let rec loop =
        function
        | Number _ as n when n = x -> r
        | Identifier _ as var when var = x -> r
        | Power(f, n) -> Power(loop f, loop n)
        | Function(fn, f) -> Function(fn, loop f)
        | Product l -> Product(List.map loop l)
        | Sum l -> Sum(List.map loop l)
        | Id (v,str) -> Id(loop v,str)
        | Definition(a,b, s) -> Definition(loop a, loop b, s)
        | Generic(a, ty) -> Generic(loop a, ty)
        | FunctionN(Probability, h::t) -> FunctionN(Probability, h::(List.map loop t))
        | Summation(fx,var,start, stop) -> summation var (loop start) (loop stop) (loop fx)
            
        | IsFunctionExpr(Identifier (Symbol _), x,ex) when doall -> fx2 (loop x) (loop ex)
        | IsFunctionExpr(Identifier (Symbol _), x,ex) -> fx2 x (loop ex)
        | FunctionN(fn, l) -> FunctionN(fn, List.map loop l)
        | IsDerivative(f, x, dx) -> FunctionN(f, [loop x; dx ])
        | x -> x
    loop f

let replaceSymbolWith r x f = replaceSymbolAux false r x f

let replaceSymbolAllWith r x f = replaceSymbolAux true r x f

let rec containsVar x =
    function
    | Identifier _ as sy when sy = x -> true
    | Power(p, n) -> containsVar x n || containsVar x p
    | Function(_, fx) -> containsVar x fx
    | Generic (y,_) -> containsVar x y
    | Definition(y,z,_) -> containsVar x y || containsVar x z
    | Id (y,_) -> containsVar x y
    | Product l | Sum l | FunctionN(_, l) -> List.exists (containsVar x) l
    | _ -> false

let rec containsAnyVar =
    function
    | Identifier _ -> true
    | Power(p, n) -> containsAnyVar n || containsAnyVar p
    | Id (fx, _)
    | Generic(fx, _)
    | Function(_, fx) -> containsAnyVar fx
    | Definition(a,b, _) -> containsAnyVar a || containsAnyVar b
    | Product l | Sum l | FunctionN(_, l) -> List.exists containsAnyVar l
    | _ -> false

let replaceSymbols (vars : seq<_>) e =
    let map = dict vars
    let rec loop = function
        | Identifier _ as var when map.ContainsKey var -> map.[var]
        | Power(f, n) -> Power(loop f, loop n)
        | Function(fn, f) -> Function(fn, loop f)
        | Id (x,strtag) -> Id(loop x, strtag)
        | Definition(a,b,s) -> Definition(loop a, loop b,s)
        | Generic(x, ty) -> Generic (loop x, ty)
        | Product l -> Product(List.map loop l)
        | Sum l -> Sum(List.map loop l)
        | FunctionN(fn, l) -> FunctionN(fn, List.map loop l)
        | x -> x
    loop e

module Structure =
    let rec width =
        function
        | Undefined
        | Constant _
        | Identifier _ -> 1
        | Generic(x,_)
        | Definition(x,_,_)
        | Id (x, _) -> width x
        | Power(x, n) -> width x + 1 + width n
        | FunctionN(fn, x::_) when functionFirstTermOnly fn -> width x + 1
        | Product l | Sum l | FunctionN(_, l) -> List.sumBy width l
        | Function(_, x) -> width x + 1
        | Approximation _ | Number _ -> 1
        | f -> failwith (sprintf "unimplemented compute size %A" (  f))

    let rec depth =
        function
        | Undefined
        | Constant _
        | Identifier _ -> 1
        | Generic(x,_)
        | Definition(x,_,_)
        | Id (x, _) -> depth x
        | Power(x, n) -> (max (depth x) (depth n)) + 1
        | FunctionN(fn, x::_) when functionFirstTermOnly fn -> depth x + 1
        | Product l | Sum l | FunctionN(_, l) -> 1 + (List.map depth l |> List.max)
        | Function(_, x) -> depth x + 1
        | Approximation _ | Number _ -> 1
        | f -> failwith ("unimplemented compute depth for " + (f.ToFormattedString()))

    let size e = width e + depth e

    ///isolate "extracts" exprToIsolate from expr by dividing expr by exprToIsolate
    ///applying hold to that result and multiplying the result by exprToIsolate
    ///This is useful for keeping vector type variables from mixing with exressions
    let isolate (exprToIsolate) expr = isolate exprToIsolate expr

    ///isolate "extracts" exprToIsolate from expr by dividing expr by exprToIsolate
    ///applying hold to that result and multiplying the result by exprToIsolate
    ///This is useful for keeping vector type variables from mixing with exressions
    ///This version adds a tag to the sealed variable. Tagged variables aren't simplified by default and require fullsimplify to be removed. They can allow more precise editing of expressions.
    let isolateTagged (exprToIsolate) tag expr = isolateTagged tag exprToIsolate expr

    ///holdAndIsolate is a common pattern where we eg multiply by a quantity we want to keep isolated.
    ///it take a binary function f, (such as multiplication) and apply it as f a (hold b) |> isolate (hold b)
    let holdAndIsolate f a b = holdAndIsolate f a b

    ///holdAndIsolate is a common pattern where we eg multiply by a quantity we want to keep isolated.
    ///it take a binary function f, (such as multiplication) and apply it as f a (hold b) |> isolate (hold b)
    ///This version adds a tag to the sealed variable. Tagged variables aren't simplified by default and require fullsimplify to be removed. They can allow more precise editing of expressions.
    let holdAndIsolateTagged f tag a b = holdAndIsolateTagged f tag a b

    let averageDepth =
        function
        | Sum l | Product l | FunctionN(_, l) -> List.averageBy (depth >> float) l
        | e -> float (depth e)

    let averageWidth =
        function
        | Sum l | Product l | FunctionN(_, l) -> List.averageBy (width >> float) l
        | e -> float (depth e)

    let rootWidth =
        function
        | Sum l | Product l -> List.length l
        | _ -> 1

    let partition func =
        function
        | Sum l ->
            let a,b = List.partition func l
            match a with
            | [] -> None, List.sum b
            | _ -> Some (List.sum a), List.sum b
        | Product l ->
            let a,b = List.partition func l
            match a with
            | [] -> None, List.reduce (*) b
            | _ -> Some(List.reduce (*) a), List.reduce (*) b
        | f -> if func f then Some f, Operators.undefined else None, f

    let filter func =
        function
        | Sum l ->
            List.filter func l
            |> List.sum
        | Product l ->
            List.filter func l
            |> List.fold (*) 1Q
        | f -> if func f then f else Operators.undefined

    let exists func =
        function
        | Sum l | Product l | FunctionN(_, l) -> List.exists func l
        | f -> func f

    let rec existsRecursive func =
        function
        | Undefined as un -> func un
        | Identifier _ as i -> func i
        | Number _ as n -> func n
        | Approximation _ as r -> func r
        | Id (x, _) as idx -> func idx || existsRecursive func x
        | Generic(x, _) as t -> func t || existsRecursive func x
        | Definition(a, b,_) as def ->
            func def || existsRecursive func a || existsRecursive func b
        | Power(p, n) as pow ->
            func pow || existsRecursive func n || existsRecursive func p
        | Function(_, fx) as f -> func f || existsRecursive func fx
        | (Product l | Sum l | FunctionN(_, l)) as expr ->
            func expr || List.exists (existsRecursive func) l
        | _ -> false

    let rec first func =
        function
        | Identifier _ as i ->
            if func i then Some i
            else None
        | Definition(a,b, _)
        | Power(a, b) as expr ->
            if func expr then Some expr
            else List.tryPick (first func) [ a; b ]
        | Id (fx, _) as f -> 
            if func f then Some f
            else first func fx
        | Generic(fx, _) 
        | Function(_, fx) as f ->
            if func f then Some f
            else first func fx
        | FunctionN(fn, x::_ ) as f when functionFirstTermOnly fn ->
            if func f then Some f
            else first func x
        | (Product l | Sum l | FunctionN(_, l)) as expr ->
            if func expr then Some expr
            else List.tryPick (first func) l
        | _ -> None

    let collectDistinctWith f expr =
        Structure.collectAllDistinct (fun x ->
            if f x then Some x
            else None) expr

    let rec recursiveFilter filter =
        function
        | Number _ as n when not (filter n) -> None
        | Number _ as n -> Some n
        | Identifier _ as var when not (filter var) -> None
        | Identifier _ as var -> Some var
        | Id (x,strtag) as e ->
            if filter e then Some e
            else Option.map (fun f -> Id(f,strtag)) (recursiveFilter filter x) 
        | Generic(x,ty) as e ->
            if filter e then Some e
            else Option.map (fun f -> Generic(f,ty)) (recursiveFilter filter x)
        | Definition(a,b,_) as e ->
            match
                (maybe {
                    let! a' = recursiveFilter filter a
                    let! b' = recursiveFilter filter b
                    return Definition(a', b',"")}) with
            | None -> if filter e then Some e else None
            | f -> f
        | Power(f, n) as p ->
            match
                (maybe {
                    let! g = recursiveFilter filter f
                    let! m = recursiveFilter filter n
                    return Power(g, m)}) with
            | None -> if filter p then Some p else None
            | f -> f
        | Product l as prod ->
            let pr = List.map (recursiveFilter filter) l
                     |> List.filterMap Option.isSome Option.get
            match pr with
            | [] -> if filter prod then Some prod else None
            | l -> Some (List.fold (*) 1Q l)
        | Sum l as sum ->
            let suml = List.map (recursiveFilter filter) l
                     |> List.filterMap Option.isSome Option.get
            match suml with
            | [] -> if filter sum then Some sum else None
            | l -> Some (List.sum l)
        | Function _
        | FunctionN _ as fn ->
            if filter fn then Some fn else None
        | _ -> None

    let recursivePartition filter f =
        let trues = recursiveFilter filter f
        let falses = recursiveFilter (filter >> not) f
        trues, falses

    let rec applyInFunctionRec fx =
        function
        | Function(fn, f) -> Function(fn, applyInFunctionRec fx f)
        | Power(x,n) -> Power(applyInFunctionRec fx x, n)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability, s::(applyInFunctionRec fx x)::rest)
        | FunctionN(fn, x::parameters) when functionFirstTermOnly fn ->
            FunctionN(fn, (applyInFunctionRec fx x)::parameters)
        | FunctionN(fn, parameters) ->
            FunctionN(fn, List.map (applyInFunctionRec fx) parameters)
        | x -> fx x

    let applyInFunction fx =
        function
        | Function(fn, f) -> Function(fn,fx f)
        | Power(x,n) -> Power(fx x, n)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability, s::fx x::rest)
        | FunctionN(fn, x::param) when functionFirstTermOnly fn ->
            FunctionN(fn, fx x::param)
        | FunctionN(fn, xs) ->
            FunctionN(fn, List.map fx xs)
        | x -> x

    let internal filterApply fx filter x = if filter x then fx x else x

    let rec recursiveMapFilter filter fx =
        function
        | Identifier _ as var when filter var -> fx var
        | Id (x,strtag) ->
            Id(recursiveMapFilter filter fx x, strtag)
            |> filterApply fx filter
        | Generic(x,ty) ->
            Generic(recursiveMapFilter filter fx x, ty)
            |> filterApply fx filter
        | Definition(a, b, _) ->
            Definition (recursiveMapFilter filter fx a, recursiveMapFilter filter fx b, "")
            |> filterApply fx filter
        | Power(f, n) ->
            Power (recursiveMapFilter filter fx f, recursiveMapFilter filter fx n)
            |> filterApply fx filter
        | Function(fn, f) ->
            Function(fn, recursiveMapFilter filter fx f)
            |> filterApply fx filter
        | Product l ->
            Product(List.map (recursiveMapFilter filter fx) l)
            |> filterApply fx filter
        | Sum l ->
            Sum(List.map (recursiveMapFilter filter fx) l)
            |> filterApply fx filter
        | FunctionN(Probability, s :: x :: rest) ->
            FunctionN(Probability, s :: recursiveMapFilter filter fx x :: rest)
            |> filterApply fx filter
        | FunctionN(fn, l) ->
            FunctionN(fn, List.map (recursiveMapFilter filter fx) l)
            |> filterApply fx filter
        | x -> filterApply fx filter x

    let recursiveMap fx e = recursiveMapFilter (fun _ -> true) fx e

    let toList =
        function
        | FunctionN(Max,l)
        | FunctionN(Min,l)
        | Sum l | Product l -> l
        | x -> [ x ]

    let listOfProduct = function
        | Product l -> l
        | f -> [f]

    let listOfSum = function
        | Sum l -> l
        | f -> [f]

    let mapRootList f =
        function
        | Sum l -> Sum(List.map f l)
        | Product l -> Product(List.map f l)
        | x -> x

    let extractNonVariablesAndApplyF x f = function
        | Product l ->
            let hasvar, consts = List.partition (containsVar x) l
            let consts' =
                match consts with
                | [] -> 1Q
                | [ x ] -> x
                | _ -> Product consts

            let vars =
                match hasvar with
                | [] -> 1Q
                | [ x ] -> x
                | _ -> Product hasvar
            consts' * f vars
        | v -> if containsVar x v then f v else v * f 1Q

    let extractConstantAndApplyF (f:Expression->Expression) = function
        | Product (IsNumber c::l) ->
            match l with
            | [] -> c
            | [x] -> c * f x
            | _ -> c * f (Product l)
        | v -> f v
            
    /// <summary>
    /// The superposition principle states that the net response at a given point in space caused by two or more stimuli is the sum of the responses that would have been caused by each stimulus individually.
    /// It can be seen as being about taking linear combinations of functions.
    /// So, if we have a function f(a + b + c) we can do f(a) + f(b) + f(c). This function checks if the given expression is a known linear function and extracts the function and applies it to each term of the sum.
    /// </summary>
    let applySuperpositionPrinciple = function 
        | IsLinearFn ((Sum l), f) -> 
            List.map (fun fx -> f fx) l |> Sum
        | f -> f
    
    let getAtLocFilter filter h v expr = 
        let rec walk ch cv = function 
        | x when ch = h && cv = v && filter x -> Some x 
        | Function(_, x) -> walk 0 (cv + 1) x   
        | Product l -> horizontal 0 (cv+1) l
        | Power(x, y) -> walk 0 (cv + 1) x |> Option.orElse (walk (ch + 1) (cv + 1) y)
        | Sum l -> horizontal 0 (cv+1) l
        | FunctionN(_,l) -> horizontal 0 (cv + 1) l
        | Id (x,_) -> walk 0 (cv + 1) x
        | _ -> None
        and horizontal ch cv = function
            | [] -> None
            | x :: xs -> 
                //printfn "%A" (Infix.format x, ch,cv)
                match walk ch cv x with 
                | Some x -> Some x
                | None -> horizontal (ch + 1) cv xs
        walk 0 0 expr

    let getAtLoc h v expr = getAtLocFilter (konst true) h v expr

    let getElementsAndLocations expr =
        let rec walk cv ch = function
        | Function(_, x) as fn -> 
            (fn, (ch, cv))::walk (cv + 1) ch x
        | Power(x, y) as pow -> 
            (pow, (ch, cv))::walk (cv + 1) ch x @ walk (cv + 1) (ch + 1) y
        | Product l as prod -> 
            (prod, (ch, cv))::List.concat (List.mapi (walk (cv + 1)) l)
        | Sum l as sum-> 
            (sum, (ch, cv))::List.concat (List.mapi (walk (cv + 1)) l)
        | FunctionN(_, l) as fn -> 
            (fn, (ch, cv))::List.concat (List.mapi (walk (cv + 1)) l)
        | Id (x,_) as idx -> 
            (idx, (ch, cv))::walk (cv + 1) ch x
        | x -> [ (x, (ch, cv)) ]
        walk 0 0 expr
          
    let getAtDepthFilter filter v expr =
        let rec walk cv =  
            function 
            | x when cv = v && filter x -> Some x
            | Function(f, x) -> walk (cv + 1) x
            | Power(x, y) -> walk (cv + 1) x |> Option.orElse (walk (cv + 1) y)
            | Product l -> List.tryPick (walk (cv + 1)) l
            | Sum l -> List.tryPick (walk (cv + 1)) l
            | FunctionN(f, l) -> List.tryPick (walk (cv + 1)) l
            | Id (x, _) -> walk (cv + 1) x
            | _ -> None
        walk 0 expr

    let getAtDepth v expr = getAtDepthFilter (konst true) v expr

    ///Tags are ignored during maps so if you want to change the tag make sure you map on Id _.
    let mapAtDepth v f (expr, substs) =
        let rec walk cv = function
            | x when cv = v ->
                let fx = f x
                (fx,  List.removeDuplicates(substs @ [(x, fx)]))
            | Function(f, x) ->
                let (x', r) = walk (cv + 1) x
                (Function (f, x'), r)
            | Power(x, y) ->
                let (x', rx) = walk (cv + 1) x
                let (y', ry) = walk (cv + 1) y
                (Power (x', y'), rx @ ry)
            | Product l ->
                let (l', r) = List.unzip (List.map (walk (cv + 1)) l)
                (Product l', List.concat r)
            | Sum l ->
                let (l', r) = List.unzip (List.map (walk (cv + 1)) l)
                (Sum l', List.concat r)
            | FunctionN(f, l) ->
                let (l', r) = List.unzip (List.map (walk (cv + 1)) l)
                (FunctionN(f, l'), List.concat r)
            | Id (x, strtag) ->
                let (x', r) = walk (cv + 1) x
                (Id (x',strtag), r)
            | x -> (x, substs)
        walk 0 expr
    
    ///Tags are ignored during maps so if you want to change the tag make sure you map on Id _.
    let mapAtLoc h v f (expr, substs) =
        let rec walk cv ch = function
            | x when ch = h && cv = v ->
                let fx = f x
                (fx, [(x, fx)])
            | Function(f, x) ->
                let (x', r) = walk (cv + 1) ch x
                (Function (f, x'), r)
            | Power(x, y) ->
                let (x', rx) = walk (cv + 1) ch x
                let (y', ry) = walk (cv + 1) (ch + 1) y
                (Power (x', y'), rx @ ry)
            | Product l ->
                let (l', r) = List.unzip (List.mapi (walk (cv + 1)) l)
                (Product l', List.concat r)
            | Sum l ->
                let (l', r) = List.unzip (List.mapi (walk (cv + 1)) l)
                (Sum l', List.concat r)
            | FunctionN(f, l) ->
                let (l', r) = List.unzip (List.mapi (walk (cv + 1)) l)
                (FunctionN(f, l'), List.concat r)
            | Id (x,strtag) ->
                let (x', r) = walk (cv + 1) ch x
                (Id (x',strtag), r)
            | x -> (x, substs)
        let res, substs' = walk 0 0 expr
        (res, List.removeDuplicates(substs @ substs'))
         
let sget h v expr = Structure.getAtLoc h v expr 

let sgetf f h v expr = Structure.getAtLocFilter f h v expr

let sgetd v expr = Structure.getAtDepth v expr

let sgetdf filter v expr = Structure.getAtDepthFilter filter v expr

let recmap = Structure.recursiveMap

let rm = recmap

let recmapf = Structure.recursiveMapFilter

let rmf = recmapf

module Expression =
    let ``rewrite 1 as x*x^-1 (=1)`` x = Product [ hold x; x ** -1]

    /// <summary>
    /// rewrite x^2 as x*x
    /// </summary>
    let expandSquare = function
        | Power(x, Number n) when n = 2N -> Product [hold x;x]
        | x -> x
      
    let isProduct =
        function
        | Product _ -> true
        | _ -> false

    let isSum =
        function
        | Sum _ -> true
        | _ -> false

    let isMinOrMax =
        function
        | FunctionN (Min,_)
        | FunctionN (Max,_) -> true
        | _ -> false

    let isVariable =
        function
        | Identifier _ -> true
        | _ -> false

    let isCompact =
        function
        | Identifier _ | Function _ | FunctionN(Probability, _) -> true
        | _ -> false

    let isSealed = function
        | Id _ -> true 
        | _ -> false

    let isNegativePower =
        function
        | Power(_, Number n) -> n < 0N
        | _ -> false

    let containsLog =
        function
        | Function(Ln, _)
        | FunctionN(Log, _) -> true
        | _ -> false

    let containsTrig =
        function
        | Function(Cos, _)
        | Function(Sin, _)
        | Function(Tan,_)
        | Function(Acos, _)
        | Function(Asin,_)
        | Function(Atan,_)
         ->
            true
        | _ -> false

    let private simplifySquareRoot (expr : Expression) =
        let simplifyNumericPower =
            function
            | Power(Number n, Number m) when m.IsInteger ->
                Expression.FromRational(n ** (int m))
            | f -> f
        let sqRootGrouping =
            function
            | (Power(x, Number n)) when n > 1N ->
                if (int n % 2 = 0) then
                    x ** (Expression.FromRational(n / 2N)), 1Q
                elif n = 3N then x, x
                else x, simplifyNumericPower (Power(x, Number(n - 2N)))
            | x -> 1Q, x
        match expr with
        | Power(x, n) when n = 1Q / 2Q ->
            match primefactorsPartial x with
            | None -> None
            | Some(pfl, n) ->
                let n, (outr, inr) =
                    n, pfl |> groupPowers id |> List.map sqRootGrouping |> List.unzip

                let isneg = n.ToInt() < 0
                Some(List.fold (*) 1Q outr * sqrt (List.fold (*) (if isneg then -1Q else 1Q) inr))
        | _ -> None

    let collectNestedSumOrProduct test l =
        let innersums, rest = List.partition test l
        let ls = List.collect Structure.toList innersums
        ls @ rest

    let rec simplifyLite =
        function
        | Sum [ x ] | Product [ x ] -> simplifyLite x
        | Power(Number n, Number m) when m.IsInteger && m <= 100_000N ->
            Expression.FromRational(n ** (int m))
        | Power(x, p) -> Power(simplifyLite x, simplifyLite p)
        | Product (n::rest) when n = 1Q -> simplifyLite (Product rest)
        | Product l ->
            Product
                (List.map simplifyLite
                     (collectNestedSumOrProduct isProduct l))
        | Sum l ->
            Sum
                (List.map simplifyLite
                     (collectNestedSumOrProduct isSum l))
        | FunctionN(Max, l) ->
            FunctionN(
                Max,
                (List.map simplifyLite
                     (collectNestedSumOrProduct isMinOrMax l)))
        | FunctionN(Min, l) ->
            FunctionN(
                Min,
                (List.map simplifyLite
                     (collectNestedSumOrProduct isMinOrMax l)))
        | FunctionN(fn, l) -> FunctionN(fn, List.map simplifyLite l)
        | Function(fn, f) -> Function(fn, simplifyLite f)
        | x -> x

    let internal simplifyaux removeseals simplifysqrt fx =
        let rec simplifyLoop =
            function
            | Power(_, Number n) when n = 0N -> 1Q
            | Power(x, Number n) when n = 1N -> simplifyLoop x
            | Power(Number x, _) when x = 1N -> 1Q
            | Power(Product [ x ], n) | Power(Sum [ x ], n) ->
                simplifyLoop (Power(x, n))
            | Power(Number n, _) when n = 0N -> 0Q
            | Power(Number n, Number m) when m.IsInteger && m <= 100_000N ->
                Expression.FromRational(n ** (int m))
            | Power(Power(x, a), b) -> simplifyLoop (Power(x, (a * b)))
            | Power(Power(a,Number n), Number m) when n = 2N && m = (1N/2N) ->
                abs (simplifyLoop a)
            | Power(x, n) as expr when n = 1Q / 2Q && simplifysqrt ->
                match simplifySquareRoot expr with
                | Some x' -> x'
                | None -> Power(simplifyLoop x, n)
            | Power(x,(Number n as p)) when n.Denominator = 2I && n <= 200_000N ->
                match simplifySquareRoot (sqrt x) with
                | Some x -> x** Operators.fromInteger n.Numerator
                | None -> Power(simplifyLoop x, simplifyLoop p)
            | Power(a, FunctionN(Log,[b;c])) when a = b -> simplifyLoop c 
            //|a|^2 -> a^2
            | Power(Function(Abs, x), Number n) when n = 2N -> simplifyLoop (x ** 2Q)
            | Power(x, n) -> Power(simplifyLoop x, simplifyLoop n)
            | Interval(a,b) -> interval (simplifyLoop a) (simplifyLoop b)
            | Function(Function.Cos, Function(Acos, x))
            | Function(Function.Acos, Function(Cos, x)) -> simplifyLoop x
            | Function(Ln, Power(Constant Constant.E, x))
            | Function(Ln, Function(Exp, x)) -> simplifyLoop x
            | Function(Floor, Number n) -> ofBigInteger (n.Numerator / n.Denominator)
            | Function(Floor, Approximation (Real r)) -> ofFloat (floorf r)
            | Function(Ceil, Number n) -> ofBigInteger (BigRational.ceil n) 
            | Function(Ceil, Approximation (Real r)) -> ofFloat (ceilf r)
            | Function (Fac, Number n)  when n = 0N -> 1Q
            | Function(Ceil, IntervalF i) -> intervalF (ceilf i.Infimum) (ceilf i.Supremum)
            | Function(Floor, IntervalF i) -> intervalF (floorf i.Infimum) (floorf i.Supremum) 
            | Function(Floor, Interval (a,b)) -> interval (simplifyLoop (floor a)) (simplifyLoop (floor b))
            | Function(Ceil, Interval (a,b)) -> interval (simplifyLoop (ceil a)) (simplifyLoop (ceil b))
            | FunctionN(Log, [_;n]) when n = 1Q -> 0Q
            | FunctionN(Log, [a;Power(b,x)]) when a = b -> simplifyLoop x
            | FunctionN(Log, [a;b]) when a = b -> 1Q
            | Power(Constant Constant.E, Function(Ln,x))
            | Function(Exp, Function(Ln, x)) -> simplifyLoop x
            | Function(f,x) when Trigonometry.isTrigonometricFunction f ->
                Trigonometry.simplifyWithTable (Function(f, (simplifyLoop x)))
            | Function(f, x) -> Function(f, (simplifyLoop x))
            | IsFunctionExpr(_,_, (IsNumber _ as n)) -> simplifyLoop n
            | IsDerivative(_, IsFunctionExpr(Identifier(Symbol fname),x,e),dx) ->
                fxn fname x (diff dx (simplifyLoop e))
            | FunctionN(Derivative, [FunctionN(SumOver,fx::exprs);dx]) ->
                FunctionN(SumOver,FunctionN(Derivative, [fx;dx])::exprs)
            | FunctionN(f, [ fx; var; a; b ]) as expr ->
                match simplifyLoop a, simplifyLoop b with
                | Number n, Number m ->
                    match f with
                    | SumOver ->
                        List.sum [ for i in n .. m -> replaceSymbolWith (Number i) var fx ] |> simplifyLoop
                    | ProductOver ->
                        List.reduce (*) [ for i in n .. m -> replaceSymbolWith (Number i) var fx ] |> simplifyLoop
                    | _ -> expr
                | a', b' ->
                    match f with
                    | SumOver
                    | ProductOver ->
                        FunctionN(f, [simplifyLoop fx; var; a'; b' ])
                    | _ -> expr
            | FunctionN(Choose,[_ ;IsInteger k]) when k = 0Q -> 1Q
            | FunctionN(Choose,[n; IsInteger k]) when k = 1Q -> n
            | FunctionN(Choose,[AsBigInteger n; AsBigInteger k]) -> Combinatorics.chooseN n k
            | FunctionN(f, l) -> FunctionN(f, List.map simplifyLoop l)
            | Product [] -> 1Q
            | Sum [] -> 0Q
            | Sum [ x ] | Product [ x ] -> simplifyLoop x
            | Product (n::rest) when n = 1Q -> simplifyLoop (Product rest)
            | Product l -> List.map simplifyLoop l |> List.fold (*) 1Q
            | Id (x,strtag) when strtag = "" || removeseals -> simplifyLoop x
            | Sum l -> List.map simplifyLoop l |> List.sum
            | IntervalF i when i.Infimum = i.Supremum -> ofFloat i.Infimum
            | Interval(a,b) when a = b -> a
            | x -> x
        simplifyLoop fx |> Rational.reduce
    
    let simplify e = simplifyaux false true e
    
    let fullSimplify e =
        e
        |> simplifyLite
        |> repeat 2 (simplifyaux true true)
        |> Rational.rationalize
        |> Algebraic.expand

    let fullsimplify e = fullSimplify e

    let fullerSimplify e =
        Trigonometry.simplify e
        |> fullSimplify
        
    let replaceWithAux autosimplify replacement expressionToFind formula =
        let tryReplaceCompoundExpression replacement
            (expressionToFindContentSet : Hashset<_>) (expressionList : _ list) =
            let expressionListSet = Hashset expressionList
            if expressionToFindContentSet.IsSubsetOf expressionListSet then
                expressionListSet.SymmetricExceptWith expressionToFindContentSet
                replacement :: List.ofSeq expressionListSet
            else expressionList

        let expressionToFindContentSet = Hashset(Structure.toList expressionToFind)

        let rec iterReplaceIn =
            function
            | Identifier _ as var when var = expressionToFind -> replacement
            | FunctionN _ | Power _ | Function _ | Number _ | Approximation _ | Constant _ as expr
                when expr = expressionToFind ->
                    replacement
            | Id (x,strtag) -> Id (iterReplaceIn x,strtag)
            | Definition(a,b, _) -> Definition(iterReplaceIn a, iterReplaceIn b, "")
            | Generic(a,ty) -> Generic(iterReplaceIn a, ty)
            | Power(p, n) -> Power(iterReplaceIn p, iterReplaceIn n)
            | Function(f, fx) -> Function(f, iterReplaceIn fx)
            | Product l ->
                Product
                    (l |> List.map iterReplaceIn
                       |> (tryReplaceCompoundExpression replacement expressionToFindContentSet))
            | Sum l ->
                Sum
                    (l |> List.map iterReplaceIn
                       |> (tryReplaceCompoundExpression replacement expressionToFindContentSet))
            | FunctionN(Probability, s::x::rest) -> FunctionN(Probability, s::iterReplaceIn x::rest)
            | Products (fx,var,start, stop) -> products (iterReplaceIn var) start stop (iterReplaceIn fx)
            | Summation (fx,var,start, stop) -> summation (iterReplaceIn var) start stop (iterReplaceIn fx)
            | FunctionN(fn, l) ->
                FunctionN (fn, List.map iterReplaceIn l)
            | x -> x
        let newexpr = iterReplaceIn (simplifyLite formula)
        if autosimplify then simplify newexpr else newexpr

    let replaceWith replacement expressionToFind formula =
        replaceWithAux true replacement expressionToFind formula

    let replace expressionsToFind formula =
        let rec loop f =
            function
            | [] -> f
            | (x,replacement)::xs -> loop (replaceWith replacement x f) xs
        loop formula expressionsToFind  

    let replaceNoSimplify expressionsToFind formula =
        let rec loop f =
            function
            | [] -> f
            | (x,replacement)::xs -> loop (replaceWithAux false replacement x f) xs
        loop formula expressionsToFind

    let contains expressionToFind formula =
        let tryFindCompoundExpression (expressionToFindContentSet : Hashset<_>)
            (expressionList : _ list) =
            let expressionListSet = Hashset expressionList
            expressionToFindContentSet.IsSubsetOf expressionListSet

        let expressionToFindContentSet = Hashset(Structure.toList expressionToFind)

        let rec iterFindIn =
            function
            | Identifier _ as var when var = expressionToFind -> true
            | Definition(a,b, _)
            | Power(a, b) as expr ->
                expr = expressionToFind || iterFindIn a || iterFindIn b
            | Generic(fx,_)
            | Id (fx, _)
            | Function(_, fx) as fn -> fn = expressionToFind || iterFindIn fx
            | Product l as prod ->
                prod = expressionToFind
                || tryFindCompoundExpression expressionToFindContentSet l
                || (List.exists iterFindIn l)
            | Sum l as sum ->
                sum = expressionToFind
                || tryFindCompoundExpression expressionToFindContentSet l
                || (List.exists iterFindIn l)
            | FunctionN(_, l) as func ->
                func = expressionToFind
                || (List.exists iterFindIn l)
            | _ -> false
        iterFindIn (simplifyLite formula)


    let rec removeSymbol x =
        function
        | Identifier _ as var when var = x -> None
        | Id (e,strtag) -> removeSymbol x e |> Option.map (fun f -> Id(f,strtag))
        | Generic(e, ty) -> removeSymbol x e |> Option.map (fun f -> Generic(f,ty))
        | Definition(a,b, _) ->
            maybe {
                let! a' = removeSymbol x a
                let! b' = removeSymbol x b
                return Definition(a', b', "")}
        | Power(f, n) ->
            maybe {
                let! g = removeSymbol x f
                let! m = removeSymbol x n
                return Power(g, m)}
        | Function(fn, f) ->
            removeSymbol x f |> Option.map (fun g -> Function(fn, g))
        | Product l ->
            Product
                (List.map (removeSymbol x) l
                 |> List.filterMap Option.isSome Option.get) |> Some
        | Sum l ->
            Sum
                (List.map (removeSymbol x) l
                 |> List.filterMap Option.isSome Option.get) |> Some
        | FunctionN(fn, l) ->
            match List.map (removeSymbol x) l
                 |> List.filterMap Option.isSome Option.get with
            | [] -> None
            | nl -> FunctionN (fn, nl) |> Some
        | x -> Some x

    let remove x f =
        let placeholder = Operators.symbol "__PLACE_HOLDER__"
        let replaced = replaceWith placeholder x f
        removeSymbol placeholder replaced

    let rec findVariables =
        function
        | Identifier _ as var -> Hashset([ var ])
        | Definition(a,b,_)
        | Power(a, b) -> findVariables a |> Hashset.union (findVariables b)
        | IsFunctionExprAny(_,x,Some b) -> Hashset([x]) |> Hashset.union (findVariables b)
        | IsFunctionExprAny(_,x,_) -> Hashset([x])
        | Product l | Sum l | FunctionN(_, l) | Tupled l ->
            Hashset(Seq.collect findVariables l)
        | Generic(x,_)
        | Id (x, _)
        | Function(_, x) -> findVariables x
        | _ -> Hashset []

    let countVariables expr = 
        let counts = Dict.ofSeq []
        let rec docount = function
            | Identifier _ as v ->  
                counts.ExpandElseAdd(v, (+) 1, 1)
            | Definition(a,b,_) | Power(a, b) ->
                docount a  
                docount b
            | IsFunctionExprAny(_,x,Some b) ->
                counts.ExpandElseAdd (x, (+) 1, 1)
                docount b
            | IsFunctionExprAny(_,x,_) ->
                counts.ExpandElseAdd (x, (+) 1, 1)
            | Product l | Sum l | FunctionN(_, l) | Tupled l ->
                l |> Seq.iter docount
            | Generic(x,_)  | Id (x,_) | Function(_, x) -> 
                docount x
            | _ -> ()

        docount expr 
        counts

    let getFirstVariable x = Seq.head (findVariables x)

    /// condition: x > 0
    let cancelAbs =
        function
        | Function(Abs, x) -> x
        | x -> x

    let isLinearIn x f =
        Polynomial.isPolynomial x f && (Polynomial.degree x f).ToFloat().Value = 1.

    ///This rewrites the expression in terms of its negation, but multiplies it with -1 so as to keep it equal, effectively pulling out a -1. Useful for cancelling sometimes.
    ///Example: -a - b becomes -1 * (a + b) = -(a+b).
    let extractNegativeOne e =
        -1Q * (Algebraic.expand (e * -1Q) )

    let isLinear vars f =
        Structure.toList f
        |> List.forall (fun es ->
            let vs = findVariables es
            let cs = vars |> List.filter vs.Contains
            cs.Length = 1)
        && vars |> List.forall (fun x -> isLinearIn x f)

    let isCertainlyMultiple tester f =
        let isMultiple =
            function
            | Number n -> n.IsInteger && tester (int n)
            | Product(Number p :: ps) -> p.IsInteger && tester (int p)
            | _ -> false
        match f with
        | f when isMultiple f -> true
        | Sum l -> List.forall isMultiple l
        | _ -> false

    let isCertainlyEven = isCertainlyMultiple (xIsMultipleOfy 2)

    let isCertainlyOdd = isCertainlyEven >> not

    //A rational function is a rational where the denominator is a polynomial and the numerator is a polynomial
    let isRationalFunction var f =
        let num, den = Rational.numerator f, Rational.denominator f
        if den = 1Q then Polynomial.isPolynomial var f
        else Polynomial.isPolynomial var num && Polynomial.isPolynomial var den

    let evaluateFunction = function
        | RealConstant _
        | Function _ as f -> Option.defaultValue f (Option.map ofFloat (Expression.toFloat f))
        | x -> x
    
    let toRational e =
        let e' = Trigonometry.simplify e |> simplify
        match e' with
        | Number(n) -> n
        | _ ->
            failwith
                (sprintf "not a number : %s => %s | %A" (e.ToFormattedString())
                     (e'.ToFormattedString()) e') 
     
    let isNumericOrVariable keepVars x =
        let keep s =
            keepVars s
            || Desc.Names.Contains s
        let rec exprTest =
            function
            | Identifier(Symbol s) when keep s -> true
            | IsNumber _ -> true
            | Function (_, IsNumber _) -> true
            | Function (_, Identifier (Symbol s)) -> keep s
            | Function (_, x) -> exprTest x
            | Power(a,b) as x -> Expression.isNumber x || (exprTest a && exprTest b)
            | Product l
            | Sum l
            | FunctionN(_, l) -> List.forall exprTest l
            | _ -> false
        exprTest x 

    ///If the expression is a number converts to a float expression instead of its symbolic form
    let evalToDecimal e =
        match (NumberProperties.Expression.toFloat e) with
        | None -> e
        | Some x -> ofFloat x

    ///If the expression is a number converts to a float expression with f applied
    let evalToDecimalFn f e =
        match (NumberProperties.Expression.toFloat e) with
        | None -> e
        | Some x -> ofFloat (f x) 
          
    ///eval with numbers or vars (optionally) are acceptable
    let evalToNumericOrVars keepVars vars x =
        let v = replaceSymbols vars x |> fullSimplify
        if isNumericOrVariable keepVars v then Some v
        else None

    ///eval with numbers or vars with special physics concepts (see Core.Desc) in the symbol name are acceptable
    let evalToNumeric vars x = evalToNumericOrVars (konst false) vars x
      
    let coarsen (var:Expression) depth e =
        let mutable i = -1
        Structure.mapAtDepth depth (fun _ -> i <- i + 1; sub var (ofInteger i)) e

    ///this is just a function that holds a and b and multiplies them. hold keeps them from being simplified 
    let dot a b = Utils.dot a b

    //A cosmetic function that given a^(n/2) rewrite it as sqrt(a)^n. It uses hold to stop the automatic simplification
    let rewritePowerSqrt = function 
        | Power(x, Number n) when n.Denominator = 2I -> hold(sqrt x) ** Expression.FromInteger(n.Numerator)
        | x -> x

    let substituteUntilDone (expr: Expression, substs: (Expression * Expression) list) : Expression =
        let rec substitute acc =
            let acc' = replace (List.map swap substs) acc
            if List.exists (fun (orig, _) -> containsVar orig acc') substs then
                substitute acc'
            else
                acc'
        substitute expr

    let isLinearFn = function 
        | IsDerivative _ -> true
        | IsIntegral _ -> true
        | Summation _ -> true
        | Sum _ -> true
        | _ -> false

module Trigonometric =
    let fullsimplify (e:Expression) =
        e |> Expression.simplifyaux true false |> Trigonometric.simplify |> Trigonometry.simplifyWithTable
        
type SimplificationLevel =
    | Low 
    | Default 
    | Mid 
    | High 
    
type Expression with
    member x.Item
        with get (i:int) = sub x (ofInteger i)

    member x.Item
        with get (i:Expression) = sub x i

    member x.Item
        with get (i:Expression, j:Expression) = subs x [i;j]

    member x.Item
        with get (i:Expression, j:Expression, k:Expression) = subs x [i;j;k]

    member x.Item
        with get (indxs:Expression list) = subs x indxs

    member x.sub(i) = sub x i

    member x.sub(indices) = subs x indices 
    
    member e.simplify(?simplificationLevel) =
        let simpllevel = defaultArg simplificationLevel SimplificationLevel.Default 
        match simpllevel with 
        | SimplificationLevel.Default -> Expression.simplify e
        | SimplificationLevel.Low -> Expression.simplifyLite e
        | SimplificationLevel.Mid -> Expression.fullSimplify e
        | SimplificationLevel.High -> Expression.fullerSimplify e

module Rational =
    open FSharp.Core.Operators
    open Prelude.Common

    let toEnglish n x =
        match x with
        | IntervalF i ->
            let (a,b) = i.Pair.ToTuple()
            let l = numberToEnglish n a
            let r = numberToEnglish n b
            $"{l} to {r}"
        | Interval(l,r) -> 
            match(Expression.toFloat l, Expression.toFloat r) with
            | Some a, Some b -> 
                let l = numberToEnglish n a
                let r = numberToEnglish n b
                $"{l} to {r}"
            | _ -> ""
        | _ ->
            match Expression.toFloat x with
            | None -> ""
            | Some f -> numberToEnglish n f

    let private simplifynumber (roundto:int) num (f:BigRational) = 
        let npow = function
            | f when f <> 0N -> Some(BigRational.floor (BigRational.log10 (abs f)))
            | _ -> None
            
        let test = function | Some x -> x < -3I || x > 3I | _ -> false 
        let fn, fd = BigRational.FromBigInt (f.Numerator), BigRational.FromBigInt (f.Denominator)
        let fpow = npow f
        if test(fpow) || test(npow fn) || test(npow fd) then
            let n = fpow.Value 
            let pow10 = if absf n < 3I then 10Q ** (ofBigInteger n) else Power(10Q, seal(ofBigInteger n))
            let num = f / (10N ** int n)  
            let numf = smartround roundto (float num)
        
            if BigRational.Abs (BigRational.log10(BigRational.Abs num) + BigRational.FromBigInt n) <= 3N then numf * pow10
            else Product[ofFloat numf ; pow10 ]
        else num

    let private simplifyAtoms roundto = function  
        | Approximation (Approximation.Real r) -> 
            simplifynumber roundto (Approximation (Approximation.Real (round roundto r))) (BigRational.fromFloat64 r)  
      
        | IntervalF i -> 
            let (l,r) = i.Pair.ToTuple() 
            let a = simplifynumber roundto (Approximation (Approximation.Real (round roundto l))) (BigRational.fromFloat64 l)
            let b = simplifynumber roundto (Approximation (Approximation.Real (round roundto r))) (BigRational.fromFloat64 r) 
            if a = b then a else Interval (a, b)
   
        | Number n as num ->
            simplifynumber roundto num n 
        | x -> x
        
    let rec simplifyNumbers (roundto : int) =
        function  
        | Interval(a,b) -> Interval(simplifyNumbers roundto a, simplifyNumbers roundto b)
        | Power(x, n) -> Power(simplifyNumbers roundto x, n)
        | Sum l -> Sum(List.map (simplifyNumbers roundto) l)
        | Product l -> 
            List.map (simplifyNumbers roundto) l 
            |> List.reduce (*)  
            |> simplifyAtoms roundto
        | Function(f, x) -> Function(f, simplifyNumbers roundto x)
        | x -> simplifyAtoms roundto x 

    let round r x =
        rm (simplifyNumbers r) x
        |> rm (Expression.evalToDecimalFn (smartround2 r))
        |> rm (simplifyNumbers r) 

    let radicalRationalize x =
        let den = Rational.denominator x
        if den <> 1Q then
            let num = Rational.numerator x
            num * den / Algebraic.expand(Algebraic.expand((den * den)))
        else x

    let rationalizeWithConjugate x =
        match Rational.denominator x with
        | Sum[a;b] as den ->
            let num = Rational.numerator x
            let den' = Sum[a; -b]
            num*den'/Algebraic.expand(Algebraic.expand(den*den'))
        | _ -> x

    let rationalizeNumeratorWithConjugate x =
        match Rational.numerator x with
        | Sum[a;b] as num ->
            let den = Rational.denominator x
            let num' = Sum[a; -b]
            Algebraic.expand(Algebraic.expand(num*num'))/(den * num')
        | _ -> x

    ///Apply a function to the numerator of any rational whose denominator <> 1
    let applyToNumerator f x =
        let num = Rational.numerator x
        let den = Rational.denominator x
        if den <> 1Q then (f num) / (Expression.simplify den)
        else x

    ///given (a+b)/x, returns a/x + b/x
    let splitSumInNumerator x =
        let n = Rational.numerator x
        let d = Rational.denominator x

        if d <> 1Q then
            match n with
            | Sum l ->
                List.map (fun e -> e / d) l |> Sum
            | _ -> x
        else x

    ///given a rational with a sum in the numerator, partitions into numerators for which f is true vs false. Eg (a+b+c)/x, returns (a+b)/x+c/x if f = ((=) c) as it splits for c only.
    let partitionSumInNumerator f x =
        let n = Rational.numerator x
        let d = Rational.denominator x

        if d <> 1Q then
            match n with
            | Sum l ->
                let split, remainGrouped = List.partition f l
                Sum remainGrouped/d + Sum(List.map (fun e -> e / d) split)
            | _ -> x
        else x

    ///given (a*b)/(c*d) return a/c * b/d
    let splitQuotientOfProducts = function 
        | Divide(x,y) ->
            printfn "here"
            match x, y with
            | Product l1, Product l2 when List.length l1 = List.length l2 ->
                let qs = List.map2 (/) l1 l2
                printfn "%A" qs
                Product (List.map hold qs)

            | _ -> x/y
        | x -> x


    let applyToDenominator f x =
        let num = Rational.numerator x
        let den = Rational.denominator x
        num / (f den)

    let consolidateNumerators = function
        | Sum l as f ->
            let denominators = Hashset(List.map Rational.denominator l)
            if denominators.Count = 1 then
               let d = Seq.head denominators
               let n = List.map Rational.numerator l |> Sum
               n / d
            else f
        | f -> f

    let groupSumsByDenominator = function
        | Sum l ->
            l |> List.groupBy Rational.denominator
              |> List.map (snd >> List.sum >> Rational.expand)
              |> Sum
        | f -> f

type Prob () =
    static member P(x) = FunctionN(Probability, [symbol "P"; x ])
    static member P(s,x) = FunctionN(Probability, [symbol s; x ])
    static member P(x,?name) =
        FunctionN(Probability, [symbol (defaultArg name "P");  x ])
    static member P(x,conditional, ?name, ?semicolon) =
        match semicolon with
        | Some true ->
            FunctionN(Probability, [symbol (defaultArg name "P");  x; conditional; Parameter ";" ])
        | _ ->
            FunctionN(Probability, [symbol (defaultArg name "P");  x; conditional])


module Func =
    ///Given a function expression with a body, returns an F# function. See also
    ///toFuncMV <see cref="M:MathNet.Symbolics.Core.toFuncMV"/>
    let toFn f =
        match f with
        | IsFunctionExpr (_, xvar, fx) -> fun x -> Expression.replaceWith x xvar fx
        | IsFunctionExpr (_, Tupled vars, fx) ->
            function
            | (Tupled xs) -> Expression.replace (List.zip vars xs) fx
            | _ -> failwith "Need tupled input. See also makefuncMV"
        | _ -> failwith "Not a function, use makefuncOfExpr instead"

    ///Given a function expression with a body and that also takes a tuple as input, returns an F# function with type: Expression list -> Expression.
    let toFnMV f =
        match f with
        | IsFunctionExpr (_, Tupled vars, fx) ->
            fun xs -> Expression.replace (List.zip vars xs) fx

        | _ -> failwith "Not a multivariate function with Tuple input, use makefunc instead"

    ///Returns an F# function given a formula expression
    let fnOfExpr xvar f =
        fun x -> Expression.replaceWith x xvar f

    ///Returns an F# function pf type Expression list -> Expression given a formula expression
    let fnOfExprMV vars f =
        fun xs -> Expression.replace (List.zip vars xs) f

    ///Given a function expression, creates a function and then applies parameter. Best for single use.
    let applyfn f x = toFn f x
     
module Ops =
    let max2 a b =
        match (a,b) with
            | PositiveInfinity, _ -> a
            | _, PositiveInfinity -> b
            | a , b when a = b -> a
            | Number n, Number m -> Expression.FromRational (max n m)
            | _ -> FunctionN(Function.Max, [a;b])
    let min2 a b =
        match (a,b) with
        | PositiveInfinity, _ -> b
        | _, PositiveInfinity -> a
        | a , b when a = b -> a
        | Number n, Number m -> Expression.FromRational (min n m)
        | _ -> FunctionN(Function.Min, [a;b])

type Ops () =
    static member max(x) = Function(Max, x)
    static member min(x) = Function(Min, x)
    static member max(a,b) = Ops.max2 a b
    static member min(a,b) = Ops.min2 a b
    static member max(xs) = FunctionN(Max, xs)
    static member min(xs) = FunctionN(Min, xs)


/// <summary>
/// Module containing functions for symbol indexing on provided expressions and variables.
/// The module includes several functions such as `createSymbolLookUp`, `eraseIndexing`, 
/// `applySymbolLookUp`, and `createLookUp` that work together to replace indexed variables with 
/// a given replacement, create look up tables with each index assigned to a corresponding index 
/// in a table, apply symbol lookup to an expression, and create a symbol lookup for the given 
/// values starting from the given start index respectively.
/// </summary>
module Indices =
    ///Given variables such as $c_1, c_2, c_3$ etc, replaces them with `replacement`.
    let eraseIndexing startIndex stopIndex replacement (var:Expression) =
        [for k in startIndex..stopIndex do var.[k], replacement]

    ///Given a symbol name, say s, creates a lookup table with each index s_i assigned to a correpsonding index in table
    let createLookUp startIndex (vals:Expression seq) (var:string) =
        let vs = Seq.toArray vals
        [for k in 0..vs.Length - 1 -> var + "_" + string (k+startIndex), vs.[k]]

    // <summary>
    /// Creates a symbol lookup for the given values starting from the given startIndex.
    /// </summary>
    /// <param name="startIndex">The start index for the variables.</param>
    /// <param name="vals">An enumerable collection of expressions.</param>
    /// <param name="var">The variable for which symbol lookup needs to be created.</param>
    let createSymbolLookUp startIndex (vals:Expression seq) (var:Expression) =
        let vs = Seq.toArray vals
        [for k in 0..vs.Length - 1 -> var.[(k+startIndex)], vs.[k]]
        
    // <summary>
    /// Creates a function that given an expression, replaces the indexed variables with the given values.
    /// </summary>
    /// <param name="startIndex">The starting index for the symbol lookup.</param>
    /// <param name="vals">A sequence of values.</param>
    /// <param name="var">A variable expression.</param
    /// <returns>A function that given an expression, replaces the indexed variables with the given values.</returns>
    let applySymbolLookUp startIndex (vals:Expression seq) (var:Expression) = 
        let vs = Seq.toArray vals
        [for k in 0..vs.Length - 1 -> var.[(k+startIndex)], vs.[k]]
        |> Expression.replace

//make a class that manages a freshvar state
///FreshVar is a class that manages the generation of fresh variables which are strings of the form x_1, x_2, x_3, etc.
/// Letter is the prefix of the variable name, e.g. x_1, x_2, x_3, etc.
/// StartIndex is the number to start counting from, e.g. 0, 1, 2, etc.
type FreshVar(?letter, ?startindex) =
    let letter = defaultArg letter "x"
    let startindex = defaultArg startindex 0
    let mutable i = startindex
    member this.next () =
        i <- i + 1
        !(sprintf $"{letter}_{i}")

    member this.Reset () = i <- 0
    member this.Current = i
    