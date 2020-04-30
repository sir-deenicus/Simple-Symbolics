module MathNet.Symbolics.Core

open MathNet.Symbolics
open MathNet.Numerics
open System 
open MathNet.Symbolics.Utils
open Prelude.Common
open MathNet.Symbolics.NumberTheory
//==========================================

let ln = Operators.ln
let arctan = Operators.arctan
let sec = Operators.sec

let symbol = Operators.symbol
let V = symbol
let sy = symbol
let mkSymbolMap l = l |> List.map (fun s -> s, symbol s) |> Map
 
let symbolString =
    function
    | Identifier(Symbol s) -> s
    | _ -> ""
 
let rec replaceSymbolAux doall r x f =
    let rec loop =
        function
        | Identifier _ as var when var = x -> r
        | Power(f, n) -> Power(loop f, loop n)
        | Function(fn, f) -> Function(fn, loop f)
        | Product l -> Product(List.map loop l)
        | Sum l -> Sum(List.map loop l)
        | Id v -> Id(loop v)
        | FunctionN(fn, l) when doall -> FunctionN(fn, List.map loop l) 
        | FunctionN(Choose, l) -> FunctionN(Choose, List.map loop l) 
        | IsFunctionExpr(Identifier (Symbol f), x,ex) -> fxn f x (loop ex)
        | IsDerivative(f, x, dx) -> FunctionN(f, [loop x; dx ])
        | x -> x
    loop f

let replaceSymbol r x f = replaceSymbolAux false r x f

let replaceSymbolAll r x f = replaceSymbolAux true r x f

let rec containsVar x =
    function
    | Identifier _ as sy when sy = x -> true
    | Power(p, n) -> containsVar x n || containsVar x p
    | Function(_, fx) -> containsVar x fx
    | Id y -> containsVar x y
    | Product l | Sum l | FunctionN(_, l) -> List.exists (containsVar x) l
    | _ -> false  

let rec containsAnyVar =
    function
    | Identifier _ -> true
    | Power(p, n) -> containsAnyVar n || containsAnyVar p
    | Id fx
    | Function(_, fx) -> containsAnyVar fx
    | Product l | Sum l | FunctionN(_, l) -> List.exists containsAnyVar l
    | _ -> false

let replaceSymbols (vars : seq<_>) e =
    let map = dict vars
    let rec loop = function
        | Identifier _ as var when map.ContainsKey var -> map.[var]
        | Power(f, n) -> Power(loop f, loop n)
        | Function(fn, f) -> Function(fn, loop f)
        | Id x -> Id(loop x)
        | Product l -> Product(List.map loop l)
        | Sum l -> Sum(List.map loop l)
        | FunctionN(fn, l) -> FunctionN(fn, List.map loop l)
        | x -> x
    loop e

let rec replaceVariableSymbol replacer =
    function
    | Identifier(Symbol s) -> Identifier(Symbol(replacer s))
    | Power(f, n) ->
        Power
            (replaceVariableSymbol replacer f,
             replaceVariableSymbol replacer n)
    | Function(fn, f) ->
        Function(fn, replaceVariableSymbol replacer f)
    | Product l ->
        Product(List.map (replaceVariableSymbol replacer) l)
    | Sum l -> Sum(List.map (replaceVariableSymbol replacer) l)
    | FunctionN(fn, l) ->
        FunctionN(fn, List.map (replaceVariableSymbol replacer) l)
    | x -> x  
   
module Structure =
    let rec width =
        function
        | Undefined
        | Constant _
        | Identifier _ -> 1
        | Power(x, n) -> width x + 1 + width n
        | FunctionN(fn, x::_) when isSpecializedFunction fn -> width x + 1
        | Product l | Sum l | FunctionN(_, l) -> List.sumBy width l
        | Function(_, x) -> width x + 1
        | Approximation _ | Number _ -> 1
        | f -> failwith (sprintf "unimplemented compute size %A" (  f))

    let rec depth =
        function
        | Undefined 
        | Constant _
        | Identifier _ -> 1
        | Power(x, n) -> (max (depth x) (depth n)) + 1
        | FunctionN(fn, x::_) when isSpecializedFunction fn -> depth x + 1
        | Product l | Sum l | FunctionN(_, l) -> 1 + (List.map depth l |> List.max)
        | Function(_, x) -> depth x + 1
        | Approximation _ | Number _ -> 1
        | f -> failwith ("unimplemented compute depth for " + (f.ToFormattedString()))

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
        | _ -> -1
    let partition func =
        function
        | Sum l -> 
            let a,b = List.partition func l   
            List.sum a, List.sum b
        | Product l -> 
            let a,b = List.partition func l  
            List.fold (*) 1Q a, List.fold (*) 1Q b 
        | f -> if func f then f, Operators.undefined else Operators.undefined, f

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
        | Power(p, n) as pow ->
            func pow || existsRecursive func n || existsRecursive func p
        | Function(_, fx) as f -> func f || existsRecursive func fx
        | (Product l | Sum l | FunctionN(_, l)) as prod ->
            func prod || List.exists (existsRecursive func) l
        | _ -> false
  
  
    let rec first func =
        function
        | Identifier _ as i ->
            if func i then Some i
            else None
        | Power(p, n) as pow ->
            if func pow then Some pow
            else List.tryPick (first func) [ p; n ]
        | Function(_, fx) as f ->
            if func f then Some f
            else first func fx 
        | FunctionN(fn, x::param::_ ) as f when isSpecializedFunction fn -> 
            if func f then Some f
            else first func x 
        | (Product l | Sum l | FunctionN(_, l)) as prod ->
            if func prod then Some prod
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
        | Definition _  
        | Identifier _ as var when not (filter var) -> None
        | Definition _ 
        | Identifier _ as var -> Some var 
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
        | Function(fn, f) -> Function(fn, fx(applyInFunctionRec fx f))
        | Power(x,n) -> Power(fx(applyInFunctionRec fx x), n)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability,
                        s::fx(applyInFunctionRec fx x)::rest)
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn ->
            FunctionN(fn, [ fx (applyInFunctionRec fx x);param ]) 
        | x -> x

    let applyInFunction fx =
        function  
        | Function(fn, f) -> Function(fn,fx f)
        | Power(x,n) -> Power(fx x, n)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability,
                            s::fx x::rest)
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn ->
            FunctionN(fn, [fx x;param ]) 
        | x -> x

    let internal filterApply fx filter x = if filter x then fx x else x

    let rec recursiveMapFilter filter fx =
        function
        | Identifier _ as var when filter var -> fx var
        | Id x -> 
            Id(recursiveMapFilter filter fx x)
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
        | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn ->
            FunctionN(fn,
                          [ recursiveMapFilter filter fx x
                            param ])
            |> filterApply fx filter
        | FunctionN(fn, l) ->
            FunctionN(fn, List.map (recursiveMapFilter filter fx) l)
            |> filterApply fx filter
        | x -> filterApply fx filter x

    let recursiveMap fx e = recursiveMapFilter (fun _ -> true) fx e

    let recursiveMapLocation depthonly filter depth breadth fx e =
        let rec loop d b =
            function
            | Identifier _ as var when d = depth && (depthonly || b = breadth)
                                       && filter var -> fx var
            | Power(f, n) when d = depth && (depthonly || b = breadth)
                               && filter (Power(f, n)) -> fx (Power(f, n))
            | Power(f, n) -> Power(loop (d + 1) 0 f, loop (d + 1) 1 n)
            | Function(fn, f) when d = depth && (depthonly || b = breadth)
                                   && filter (Function(fn, f)) ->
                fx (Function(fn, f))
            | Function(fn, f) -> Function(fn, loop (d + 1) 0 f)
            | Product l when d = depth && (depthonly || b = breadth)
                             && filter (Product l) -> fx (Product l)
            | Product l -> Product(List.mapi (loop (d + 1)) l)
            | Sum l when d = depth && (depthonly || b = breadth) && filter (Sum l) ->
                fx (Sum l)
            | Sum l -> Sum(List.mapi (loop (d + 1)) l)
            | x -> x
        loop 0 0 e

    let recursiveMapDepth filter depth fx e =
        recursiveMapLocation true filter depth 0 fx e

    let mapfirstN n func expr =
        let mutable count = 0
        recursiveMapFilter (fun _ -> count < n) (function
            | f when count < n ->
                let f' = func f
                if f' <> f then count <- count + 1
                f'
            | f -> f) expr 
    
    let mapfirst func expr =
        let mutable isdone = false
        recursiveMap (function
            | f when not isdone ->
                let f' = func f
                isdone <- f' <> f
                f'
            | f -> f) expr  

    let toList =
        function
        | FunctionN(Max,l)
        | FunctionN(Min,l)
        | Sum l | Product l -> l
        | x -> [ x ]

    let listOfProduct= function
        | Product l -> l
        | f -> [f]    

    let listOfSum= function
        | Sum l -> l
        | f -> [f]

    let mapList f =
        function
        | Sum l -> Sum(List.map f l)
        | Product l -> Product(List.map f l)
        | x -> x


let recmap = Structure.recursiveMap

let recmapf = Structure.recursiveMapFilter

module Expression =  
    let evaluateFloat vars expr =
        let map =
            Seq.map (fun (x, y) -> symbolString x, FloatingPoint.Real y) vars
        let symbvals = System.Collections.Generic.Dictionary(dict map)
        try
            Some(let v = Evaluate.evaluate symbvals expr in v.RealValue)
        with _ -> None 

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

    let isNegativePower =
        function
        | Power(_, Number n) -> n < 0N
        | _ -> false  

    let containsLog =
        function
        | Function(Ln, _) -> true
        | _ -> false

    let containsTrig =
        function
        | Function(Cos, _) 
        | Function(Sin, _) 
        | Function(Acos, _) 
        | Function(Asin,_) 
        | Function(Atan,_) 
        | Function(Tan,_) ->
            true
        | _ -> false 

    let expandSumsOrProducts f = function
        | Sum l -> l |> List.map f |> Sum
        | Product l -> l |> List.map f |> Product
        | x -> x

    let extractConstant f = function
        | Product (c::l) when Expression.isNumber c ->
            match l with
            | [] -> c
            | [x] -> c * f x
            | _ -> c * f (Product l)
        | x -> x

    let extractNonVariables x f = function
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

    let simplifyNumericPower =
        function
        | Power(Number n, Number m) when m.IsInteger ->
            Expression.FromRational(n ** (int m))
        | f -> f

    let simplifySquareRoot (expr : Expression) =
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
        | Power(Number n, Number m) when m.IsInteger ->
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

    let simplify simplifysqrt fx =
        let rec simplifyLoop =
            function
            | Power(x, Number n) when n = 1N -> simplifyLoop x
            | Power(Number x, _) when x = 1N -> 1Q
            | Power(Product [ x ], n) | Power(Sum [ x ], n) ->
                simplifyLoop (Power(x, n))
            | Power(Number n, Number m) when m.IsInteger ->
                Expression.FromRational(n ** (int m))
            | Power(Power(x, a), b) -> simplifyLoop (Power(x, (a * b)))
            | Power(x, n) as expr when n = 1Q / 2Q && simplifysqrt ->
                match simplifySquareRoot expr with
                | Some x' -> x'
                | None -> Power(simplifyLoop x, n)
            | Power(a, FunctionN(Log,[b;c])) when a = b -> simplifyLoop c 
            | Power(x, n) -> Power(simplifyLoop x, simplifyLoop n)
            | Function(Atan, Number n) when n = 1N -> Operators.pi / 4
            | Function(Atan, Number n) when n = 0N -> 0Q
            | Function(Cos, Product [ Number n; Constant Pi ]) when n = (1N / 2N) ->
                0Q
            | Function(Sin, Product [ Number n; Constant Pi ]) when n = (1N / 2N) ->
                1Q
            | Function(Cos, Product [ Number n; Constant Pi ]) when n = 1N / 4N ->
                1Q / sqrt (2Q)
            | Function(Sin, Product [ Number n; Constant Pi ]) when n = 1N / 4N ->
                1Q / sqrt (2Q)
            | Function(Function.Cos, Function(Acos, x))
            | Function(Function.Acos, Function(Cos, x)) -> simplifyLoop x
            | Function(Ln, Power(Constant Constant.E, x))
            | Function(Ln, Function(Exp, x)) -> simplifyLoop x
            | FunctionN(Log, [_;n]) when n = 1Q -> 0Q
            | FunctionN(Log, [a;Power(b,x)]) when a = b -> simplifyLoop x 
            | FunctionN(Log, [a;b]) when a = b -> 1Q
            | Power(Constant Constant.E, Function(Ln,x))
            | Function(Exp, Function(Ln, x)) -> simplifyLoop x
            | Function(f, x) -> Function(f, (simplifyLoop x))
            | IsFunctionExpr(_,_, (IsNumber _ as n)) -> simplifyLoop n
            | IsDerivative(_, IsFunctionExpr(Identifier(Symbol f),x,e),dx) -> 
                fxn f x (diff dx (simplifyLoop e))   
            | FunctionN(Derivative, [FunctionN(SumOver,fx::exprs);dx]) ->
                FunctionN(SumOver,FunctionN(Derivative, [fx;dx])::exprs)
            | FunctionN(f, [ fx; var; a; Identifier(Symbol "="); b ]) as expr ->
                match simplifyLoop a, simplifyLoop b with
                | Number n, Number m ->
                    match f with
                    | SumOver ->
                        List.sum [ for i in n .. m -> replaceSymbol (Number i) var fx ] |> simplifyLoop
                    | ProductOver ->
                        List.reduce (*) [ for i in n .. m -> replaceSymbol (Number i) var fx ]
                    | _ -> expr
                | a', b' -> 
                    match f with
                    | SumOver
                    | ProductOver ->
                        FunctionN(f, [simplifyLoop fx; var; a'; Identifier(Symbol "="); b' ]) 
                    | _ -> expr
            | FunctionN(Choose,[Number n;Number k]) -> 
                if n < k then 0Q  
                else Number(factorial n/(factorial k * factorial(n - k)))
            | FunctionN(f, l) -> FunctionN(f, List.map simplifyLoop l)
            | Product [] -> 1Q
            | Sum [] -> 0Q
            | Sum [ x ] | Product [ x ] -> simplifyLoop x
            | Product (n::rest) when n = 1Q -> simplifyLoop (Product rest)
            | Product l -> List.map simplifyLoop l |> List.fold (*) 1Q
            | Id x -> simplifyLoop x
            | Sum l -> List.map simplifyLoop l |> List.sum
            | x -> x
        simplifyLoop fx |> Rational.reduce

    let replaceExpressionRaw autosimplify replacement expressionToFind formula =
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
            | FunctionN _ | Power _ | Function _ | Number _ | Constant _ as expr 
                when expr = expressionToFind ->
                    replacement
            | Id x -> Id (iterReplaceIn x)
            | Power(p, n) -> Power(iterReplaceIn p, iterReplaceIn n)
            | Function(f, fx) -> Function(f, iterReplaceIn fx)
            | Product l ->
                Product
                    (l |> List.map iterReplaceIn
                       |> (tryReplaceCompoundExpression replacement
                              expressionToFindContentSet))
            | Sum l ->
                Sum
                    (l |> List.map iterReplaceIn
                       |> (tryReplaceCompoundExpression replacement
                              expressionToFindContentSet))
            | FunctionN(Probability, s::x::rest) -> FunctionN(Probability, s::iterReplaceIn x::rest) 
            | FunctionN(fn, [ x; param ]) when isSpecializedFunction fn -> FunctionN(fn, [iterReplaceIn x; param])
            | FunctionN(fn, l) ->
                FunctionN (fn, List.map iterReplaceIn l)
            | x -> x
        let newexpr = iterReplaceIn (simplifyLite formula)  
        if autosimplify then simplify true newexpr else newexpr

    let replaceExpression = replaceExpressionRaw true 

    let replaceExpressions expressionsToFind formula = 
        let rec loop f =
            function 
            | [] -> f
            | (x,replacement)::xs -> loop (replaceExpression replacement x f) xs
        loop formula expressionsToFind

    let containsExpression expressionToFind formula =
        let tryFindCompoundExpression (expressionToFindContentSet : Hashset<_>)
            (expressionList : _ list) =
            let expressionListSet = Hashset expressionList
            expressionToFindContentSet.IsSubsetOf expressionListSet

        let expressionToFindContentSet = Hashset(Structure.toList expressionToFind)

        let rec iterFindIn =
            function
            | Identifier _ as var when var = expressionToFind -> true
            | Power(p, n) as powr ->
                powr = expressionToFind || iterFindIn p || iterFindIn n
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

    let removeExpression x f =
        let placeholder = Operators.symbol "__PLACE_HOLDER__"
        let replaced = replaceExpression placeholder x f
        removeSymbol placeholder replaced
    
    let rec findVariables =
        function
        | Identifier _ as var -> Hashset([ var ])
        | Power(x, n) -> findVariables x |> Hashset.union (findVariables n)
        | IsFunctionExprAny(_,x,_) -> Hashset([x])
        | Product l | Sum l | FunctionN(_, l) ->
            Hashset(Seq.collect findVariables l)
        | Function(_, x) -> findVariables x
        | _ -> Hashset []

    let getFirstVariable x = Seq.head (findVariables x)

    /// condition: x > 0
    let cancelAbs =
        function
        | Function(Abs, x) -> x
        | x -> x  

    
    let isLinearIn x f =
        Polynomial.isPolynomial x f && (Polynomial.degree x f).ToFloat() = 1.

    let xor a b = (a && not b) || (not a && b)

    let isLinear vars f =
        Structure.toList f
        |> List.forall (fun es -> 
            let vs = findVariables es
            let cs = vars |> List.filter vs.Contains
            cs.Length = 1)
        && vars |> List.forall (fun x -> isLinearIn x f) 

module Rational = 
    let rec simplifyNumbers(roundto : int) =
        function
        | Approximation (Approximation.Real r) -> 
            Approximation (Approximation.Real (round roundto r))
        | Number n as num ->
            let f = float n
            let pf = abs f
            if pf > 10000. || pf < 0.0001 then
                let p10 = floor (log10 pf)
                let x = Math.Round(f / 10. ** p10, roundto) |> Expression.fromFloat
                Product [ x
                          Power(10Q, p10 |> Expression.fromFloat) ]
            else num
        | Power(x, n) -> Power(simplifyNumbers roundto x, n)
        | Sum l -> Sum(List.map (simplifyNumbers roundto) l)
        | Product l -> Product(List.map (simplifyNumbers roundto) l)
        | Function(f, x) -> Function(f, simplifyNumbers roundto x)
        | x -> x

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

    let applyToNumerator f x =
        let num = Rational.numerator x
        let den = Rational.denominator x
        (f num) / den

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

type Expression with
    static member groupInSumWith var = function
        | Sum l -> 
            let haves, nots = List.partition (Expression.containsExpression var) l
            Product[var; haves |> List.sumBy (fun x -> x/var)] + Sum nots
        | f -> f 

    static member toRational e =
        let e' = Trigonometric.simplify e |> Expression.simplify true
        match e' with
        | Number(n) -> n
        | _ ->
            failwith
                (sprintf "not a number : %s => %s | %A" (e.ToFormattedString())
                     (e'.ToFormattedString()) e')

    static member Simplify e =
        Expression.simplify true e

    static member FullSimplify e =
        e
        |> Expression.simplifyLite
        |> Expression.simplify true
        |> Expression.simplify true
        |> Rational.rationalize
        |> Algebraic.expand

    static member FullerSimplify e =
        Trigonometric.simplify e
        |> Expression.FullSimplify


type Equation(leq : Expression, req : Expression) =
    member __.Definition = leq, req
    member __.Left = leq
    member __.Right = req
    member __.Equalities =
        [ leq, req
          req, leq ]
    
    static member ApplyToRight f (eq:Equation) = 
        let leq, req = eq.Definition
        Equation(leq, f req)
    static member ApplyToLeft f (eq:Equation) = 
        let leq, req = eq.Definition
        Equation(f leq, req)
    static member Apply f (eq:Equation) = 
        let leq, req = eq.Definition
        Equation(f leq, f req)
    static member (-) (eq : Equation, expr : Expression) =
        Equation(eq.Left - expr, eq.Right - expr)
    static member (+) (eq : Equation, expr : Expression) =
        Equation(eq.Left + expr, eq.Right + expr)
    static member (*) (eq : Equation, expr : Expression) =
        Equation(eq.Left * expr, eq.Right * expr)
    static member (/) (eq : Equation, expr : Expression) =
        Equation(eq.Left / expr, eq.Right / expr)
    override __.ToString() =
        leq.ToFormattedString() + " = " + req.ToFormattedString()

module InEquality =
    type Comparer =
        | Lesser
        | Greater
        | Geq
        | Leq
        override t.ToString() =
            match t with
            | Lesser -> "<"
            | Greater -> ">"
            | Leq ->
                match expressionFormat with
                | InfixFormat -> " ≤ "
                | _ -> " \\leq "
            | Geq ->
                match expressionFormat with
                | InfixFormat -> " ≥ "
                | _ -> " \\geq "

    let flipComparer =
        function
        | Lesser -> Greater
        | Greater -> Lesser
        | Leq -> Geq
        | Geq -> Leq

    type NumSign =
        | Positive
        | Negative
        | Nil

type InEquality(comparer : InEquality.Comparer, leq : Expression, req : Expression, ?existingConditions : InEquality seq, ?existingSigns) =
    let conditions = defaultArg (Option.map (fun (h:seq<InEquality>) -> Hashset(h)) existingConditions) (Hashset<InEquality>())
    let varsigns = defaultArg existingSigns (Dict<Expression, InEquality.NumSign>())

    member __.Definition = leq, comparer, req
    member __.Left = leq
    member __.Right = req
    member __.Comparer = comparer
    member __.VarSigns = varsigns
    member __.Conditions = Seq.toArray conditions

    member __.GetSign =
        match req with
        | Function(Abs, _) ->
            match comparer with
            | InEquality.Geq | InEquality.Greater -> Some(InEquality.Positive)
            | _ -> None
        | IsNumber n ->
            let isNegativeOrZero = Expression.isNegativeOrZeroNumber n
            if isNegativeOrZero then
                let num = n.ToFloat()
                match comparer with
                | InEquality.Leq when num < 0. -> Some(InEquality.Negative)
                | InEquality.Lesser -> Some(InEquality.Negative)
                | InEquality.Geq | InEquality.Greater when num = 0. ->
                    Some(InEquality.Positive)
                | _ -> None
            else
                match comparer with //is positive
                | InEquality.Geq | InEquality.Greater ->
                    Some(InEquality.Positive)
                | _ -> None
        | _ -> None

    override __.ToString() =
        leq.ToFormattedString() + string comparer + req.ToFormattedString()
        + newline() + (Seq.map string conditions |> String.concat (newline()))

    member i.Flip() = i.To(InEquality.flipComparer comparer, req, leq)
    member i.ApplyToRight f = i.To(i.Left, f i.Right)
    member i.ApplyToLeft f = i.To(f i.Left, i.Right)
    member i.Apply f = i.To(f i.Left, f i.Right)
    
    static member applyToRight f (e:InEquality) = e.ApplyToRight f
    static member applyToLeft f (e:InEquality) = e.ApplyToLeft f 
    static member apply f (e:InEquality) = e.Apply f 

    member i.AddCondition(c : InEquality) =
        match c.Left with
        | Identifier _ as x ->
            match c.GetSign with
            | None -> ()
            | Some s -> varsigns.Add(x, s)
        | _ -> ()
        conditions.Add c |> ignore; i

    static member decideComparison (eq : InEquality, expr : Expression) =
        let isnum = Expression.isNumber expr

        let c, safe =
            match Expression.isNegativeNumber expr, eq.VarSigns.tryFind expr with
            | false, Some InEquality.Negative | true, _ ->
                InEquality.flipComparer eq.Comparer, true
            | false, Some InEquality.Positive | _ when isnum ->
                eq.Comparer, true
            | _ -> eq.Comparer, false
        let cond =
            if not safe then
                Some (InEquality(InEquality.Comparer.Greater, expr, 0Q))
            else None
        c, cond

    member eq.To (l, r) = 
        InEquality(eq.Comparer, l, r, eq.Conditions, eq.VarSigns)
    member eq.To (comparer,l, r)  = 
        InEquality(comparer, l, r, eq.Conditions, eq.VarSigns)

    static member (*) (eq : InEquality, expr : Expression) = 
        let comparer, cond = InEquality.decideComparison (eq, expr)
        let ineq = eq.To(comparer, eq.Left * expr, eq.Right * expr)
        match cond with 
        | None -> ineq 
        | Some c -> ineq.AddCondition c
        
    static member (+) (eq : InEquality, expr : Expression) =
        eq.To(eq.Left + expr, eq.Right + expr)
    static member (-) (eq : InEquality, expr : Expression) =
        eq.To(eq.Left - expr, eq.Right - expr)
    static member (/) (eq : InEquality, expr : Expression) =
        let comparer, cond = InEquality.decideComparison (eq, expr)
        let ineq =
            eq.To(comparer, eq.Left / expr, eq.Right / expr)
        match cond with None -> ineq | Some c -> ineq.AddCondition c 

let leq a b = InEquality(InEquality.Comparer.Leq,a,b)
let geq a b = InEquality(InEquality.Comparer.Geq,a,b)
let lt a b = InEquality(InEquality.Comparer.Lesser,a,b)
let gt a b = InEquality(InEquality.Comparer.Greater,a,b) 

module Equation =
    let swap (eq:Equation) = Equation(swap eq.Definition) 
    let right (eq:Equation) = eq.Right
    let left (eq:Equation) = eq.Left

let (<=>) a b = Equation(a, b)

let equals a b = Equation(a, b)

let eqapply = Equation.Apply >> Op

let eqapplys (s,f) = Instr(Equation.Apply f, s)
  
let equationTrace (current:Equation) (instructions : _ list) = 
    stepTracer false true string current instructions

let inEqualityTrace (current:InEquality) (instructions : _ list) = 
    stepTracer false true string current instructions
      
let evalExpr vars x =
    replaceSymbols vars x |> Expression.FullerSimplify |> Some  

let evalExprNum vars x =
    let nums = vars |> Seq.filter (snd >> containsAnyVar >> not) 
    if Seq.isEmpty nums then None
    else let symb = replaceSymbols nums x |> Expression.FullSimplify
         if containsAnyVar symb then None else Some symb 
         
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
    let F = V"F"
    let G = V"G"
    let J = V "J"
    let K = V "K"
    let L = V "L"
    let M = V "M"
    let N = V "N"
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

    let ofChar (c:char) = symbol (string c) 

type Vars() = 
    //Α α, Β β, Γ γ, Δ δ, Ε ε, Ζ ζ, Η η, Θ θ, Ι ι, Κ κ, Λ λ, Μ μ, Ν ν, Ξ ξ, Ο ο, Π π, Ρ ρ,  σ,Ω ω.
    static member internal letter greek latex =
        match expressionFormat with 
        | InfixFormat -> greek
        | _ -> latex
    static member D = V"D"
    static member I = V"I"
    static member alpha = Vars.letter "α" "\\alpha" |> V
    static member beta = Vars.letter "β" "\\beta" |> V
    static member gamma = Vars.letter "γ" "\\gamma" |> V
    static member Gamma = Vars.letter "Γ" "\\alpha" |> V
    static member delta = Vars.letter "δ" "\\delta" |> V
    static member Delta = Vars.letter "Δ" "\\Delta"  |> V
    static member epsilon = Vars.letter "ε" "\\epsilon" |> V
    static member Lambda = Vars.letter "Λ" "\\Lambda" |> V
    static member lambda = Vars.letter "λ" "\\lambda" |> V
    static member mu = Vars.letter "μ" "\\mu" |> V
    static member nu = Vars.letter "v" "\\nu" |> V
    static member Theta = Vars.letter "Θ" "\\Theta" |> V
    static member theta = Vars.letter "θ" "\\theta" |> V
    static member rho = Vars.letter "ρ" "\\rho" |> V
    static member sigma = Vars.letter "σ" "\\sigma" |> V
    static member omega = Vars.letter "ω" "\\omega" |> V
    static member Omega = Vars.letter "Ω" "\\Omega" |> V
    

let rec replaceWithIntervals (defs : seq<Expression * IntSharp.Types.Interval>) e =
    let map = dict defs 
    let rec replace = function
        | IsNumber n -> 
            IntSharp.Types.Interval.FromDoubleWithEpsilonInflation (n.ToFloat())
            |> Some
        | Identifier _ as v when map.ContainsKey v -> Some map.[v]
        | Sum l -> 
            List.map replace l 
            |> List.filterMap Option.isSome Option.get 
            |> List.sum 
            |> Some
        | Product l ->
            List.map replace l 
            |> List.filterMap Option.isSome Option.get 
            |> List.fold (*)
                    (IntSharp.Types.Interval.FromDoublePrecise 1.)
            |> Some
        | FunctionN(Max, l) ->
            match l with
            | l' when (l' |> List.forall Expression.isNumber) ->
                let largest = l' |> List.map (fun x -> x.ToFloat()) |> List.max
                IntSharp.Types.Interval.FromDoubleWithEpsilonInflation largest
                |> Some
            | _ -> None
        | _ -> None
    replace e     
     

type Fn () =
    static member prob(x) = FunctionN(Probability, [symbol "P"; x ])
    static member prob(s,x) = FunctionN(Probability, [symbol s; x ]) 
    static member prob(x,?name) =
        FunctionN(Probability, [symbol (defaultArg name "P");  x ])
    static member prob(x,conditional, ?name, ?semicolon) =
        match semicolon with 
        | Some true -> 
            FunctionN(Probability, [symbol (defaultArg name "P");  x; conditional; Parameter ";" ])
        | _ ->
            FunctionN(Probability, [symbol (defaultArg name "P");  x; conditional])

type PiSigma(expr) =
    member private __.op operator y = function
        | FunctionN(f, [fx;var;start; stop]) -> 
            FunctionN(f, [operator fx y;var;start; stop])
        | x -> x

    static member Σ fx = FunctionN(SumOver, [fx;Parameter "";Parameter ""; Parameter "" ])
    static member Σ (fx,start) = FunctionN(SumOver, [fx;Vars.i;start; Vars.n])
    static member Σ (fx,start,stop) = FunctionN(SumOver, [fx;Vars.i;start; stop])
    static member Σ (fx,var,start,stop) = FunctionN(SumOver, [fx;var;start;stop]) 
    static member Π fx = FunctionN(ProductOver, [fx;Vars.i;0Q;Vars.n])
    static member (/) (a:PiSigma, b : Expression) = b * (a.op (/) b a.Expression)

    static member Evaluate(expr, ?parameters) =
        match expr, parameters with
        | FunctionN(SumOver, [ fx; var; Number n; Number m ]), _ ->
            List.sum [ for i in n .. m -> replaceSymbol (Number i) var fx ]
        | FunctionN(ProductOver, [ fx; var; Number n; Number m ]), _ ->
            List.reduce (*) [ for i in n .. m -> replaceSymbol (Number i) var fx ]
        | FunctionN(SumOver as f, [ fx; var; a; b ]), Some p
        | FunctionN(ProductOver as f, [ fx; var; a; b ]), Some p ->
            let lookup = dict p

            let runvar e =
                e
                |> replaceSymbols [ for (a, b) in p -> a, Operators.fromRational b ]
                |> Expression.toRational
                |> Option.get

            let n, m =
                match Expression.FullSimplify a, Expression.FullSimplify b with
                | Number n, Number m -> n, m
                | Number n, y -> n, runvar y
                | x, Number m -> lookup.[x], m
                | _ -> lookup.[a], runvar b

            match f with
            | SumOver ->
                List.sum [ for i in n .. m -> replaceSymbol (Number i) var fx ]
            | ProductOver ->
                List.reduce (*) [ for i in n .. m -> replaceSymbol (Number i) var fx ]
            | _ -> expr
        | FunctionN(f, [ fx; var; a; b ]), None ->
            match Expression.FullSimplify a, Expression.FullSimplify b with
            | Number n, Number m ->
                match f with
                | SumOver ->
                    List.sum [ for i in n .. m -> replaceSymbol (Number i) var fx ]
                | ProductOver ->
                    List.reduce (*) [ for i in n .. m -> replaceSymbol (Number i) var fx ]
                | _ -> expr
            | _ -> expr
        | _ -> expr  
    member __.Expression = expr 
    member __.Evaluate( ?parameters ) = 
        match parameters with 
        | None -> PiSigma.Evaluate(expr) 
        | Some par -> PiSigma.Evaluate(expr, par) 
   
let makefunc f x =
    match f with
    | IsFunctionExpr(_, xvar,fx) -> 
        replaceSymbol x xvar fx
    | _ -> f

let makefunc2 xvar f =  
    fun x -> replaceSymbol x xvar f 

let applyfn f x = makefunc x f

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
    static member max(a,b) = Ops.max2 a b


    

