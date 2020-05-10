module MathNet.Symbolics.Core

open MathNet.Symbolics
open MathNet.Numerics
open System 
open MathNet.Symbolics.Utils
open Prelude.Common
open MathNet.Symbolics.NumberTheory
open Utils.FunctionHelpers

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
        | Definition(a,b) -> Definition(loop a, loop b)
        | Generic(a, ty) -> Generic(loop a, ty) 
        | FunctionN(Probability, h::t) -> FunctionN(Probability, h::(List.map loop t))  
        | IsFunctionExpr(Identifier (Symbol _), x,ex) when doall -> fn (loop x) (loop ex)
        | IsFunctionExpr(Identifier (Symbol _), x,ex) -> fn x (loop ex)
        | FunctionN(fn, l) -> FunctionN(fn, List.map loop l) 
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
    | Generic (y,_) -> containsVar x y
    | Definition(y,z) -> containsVar x y || containsVar x z
    | Id y -> containsVar x y
    | Product l | Sum l | FunctionN(_, l) -> List.exists (containsVar x) l
    | _ -> false  

let rec containsAnyVar =
    function
    | Identifier _ -> true
    | Power(p, n) -> containsAnyVar n || containsAnyVar p
    | Id fx
    | Generic(fx, _)
    | Function(_, fx) -> containsAnyVar fx
    | Definition(a,b) -> containsAnyVar a || containsAnyVar b
    | Product l | Sum l | FunctionN(_, l) -> List.exists containsAnyVar l
    | _ -> false

let replaceSymbols (vars : seq<_>) e =
    let map = dict vars
    let rec loop = function
        | Identifier _ as var when map.ContainsKey var -> map.[var]
        | Power(f, n) -> Power(loop f, loop n)
        | Function(fn, f) -> Function(fn, loop f)
        | Id x -> Id(loop x)
        | Definition(a,b) -> Definition(loop a, loop b)
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
        | Definition(x,_) 
        | Id x -> width x
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
        | Definition(x,_) 
        | Id x -> depth x 
        | Power(x, n) -> (max (depth x) (depth n)) + 1
        | FunctionN(fn, x::_) when functionFirstTermOnly fn -> depth x + 1
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
        | Id x 
        | Generic(x, _) as t -> func t || existsRecursive func x
        | Definition(a, b) as def ->
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
        | Definition(a,b)
        | Power(a, b) as expr ->
            if func expr then Some expr
            else List.tryPick (first func) [ a; b ]
        | Generic(fx, _)
        | Id fx
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
        | Id x as e -> 
            if filter e then Some e 
            else Option.map Id (recursiveFilter filter x)
        | Generic(x,ty) as e -> 
            if filter e then Some e 
            else Option.map (fun f -> Generic(f,ty)) (recursiveFilter filter x)
        | Definition(a,b) as e -> 
            match 
                (maybe {
                    let! a' = recursiveFilter filter a  
                    let! b' = recursiveFilter filter b  
                    return Definition(a', b')}) with
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
        | Function(fn, f) -> Function(fn, fx(applyInFunctionRec fx f))
        | Power(x,n) -> Power(fx(applyInFunctionRec fx x), n)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability, s::fx(applyInFunctionRec fx x)::rest)
        | FunctionN(fn, parameters) ->
            FunctionN(fn, List.map (applyInFunctionRec fx >> fx) parameters) 
        | x -> x

    let applyInFunction fx =
        function  
        | Function(fn, f) -> Function(fn,fx f)
        | Power(x,n) -> Power(fx x, n)
        | FunctionN(Probability, s::x::rest) ->
            FunctionN(Probability, s::fx x::rest)
        | FunctionN(fn, xs) ->
            FunctionN(fn, List.map fx xs) 
        | x -> x

    let internal filterApply fx filter x = if filter x then fx x else x

    let rec recursiveMapFilter filter fx =
        function
        | Identifier _ as var when filter var -> fx var
        | Id x -> 
            Id(recursiveMapFilter filter fx x)
            |> filterApply fx filter
        | Generic(x,ty) -> 
            Generic(recursiveMapFilter filter fx x, ty)
            |> filterApply fx filter
        | Definition(a, b) ->
            Definition (recursiveMapFilter filter fx a, recursiveMapFilter filter fx b)
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
     
    let mapfirstN n filter map expr =
        let mutable count = 0
        recursiveMapFilter (fun x -> count < n && filter x) (function
            | f when count < n ->
                let f' = map f
                if f' <> f then count <- count + 1
                f'
            | f -> f) expr 
    
    let mapfirst filter map expr = mapfirstN 1 filter map expr

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

let recmap = Structure.recursiveMap

let recmapf = Structure.recursiveMapFilter

module Expression =   
    let rewriteAsOne x = Product [ x; x ** -1] 

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
            | Power(x,(Number n as p)) when n.Denominator = 2I -> 
                match simplifySquareRoot (sqrt x) with 
                | Some x -> x** Operators.fromInteger n.Numerator
                | None -> Power(simplifyLoop x, simplifyLoop p)
            | Power(a, FunctionN(Log,[b;c])) when a = b -> simplifyLoop c 
            | Power(x, n) -> Power(simplifyLoop x, simplifyLoop n)
            | Function(Function.Cos, Function(Acos, x))
            | Function(Function.Acos, Function(Cos, x)) -> simplifyLoop x
            | Function(Ln, Power(Constant Constant.E, x))
            | Function(Ln, Function(Exp, x)) -> simplifyLoop x
            | FunctionN(Log, [_;n]) when n = 1Q -> 0Q
            | FunctionN(Log, [a;Power(b,x)]) when a = b -> simplifyLoop x 
            | FunctionN(Log, [a;b]) when a = b -> 1Q
            | Power(Constant Constant.E, Function(Ln,x))
            | Function(Exp, Function(Ln, x)) -> simplifyLoop x
            | Function(f,x) when Trigonometry.isTrigonometricFunction f -> 
                Trigonometry.simplifyTrigTerm (Function(f, (simplifyLoop x)))
            | Function(f, x) -> Function(f, (simplifyLoop x))
            | IsFunctionExpr(_,_, (IsNumber _ as n)) -> simplifyLoop n
            | IsDerivative(_, IsFunctionExpr(Identifier(Symbol _),x,e),dx) -> 
                fn x (diff dx (simplifyLoop e))   
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

    let replaceExpressionAux autosimplify replacement expressionToFind formula =
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
            | Definition(a,b) -> Definition(iterReplaceIn a, iterReplaceIn b)
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
            | FunctionN(fn, l) ->
                FunctionN (fn, List.map iterReplaceIn l)
            | x -> x
        let newexpr = iterReplaceIn (simplifyLite formula)  
        if autosimplify then simplify true newexpr else newexpr

    let replaceExpression = replaceExpressionAux true 

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
            | Definition(a,b)
            | Power(a, b) as expr ->
                expr = expressionToFind || iterFindIn a || iterFindIn b
            | Generic(fx,_)
            | Id fx
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
        | Id e -> removeSymbol x e |> Option.map Id
        | Generic(e, ty) -> removeSymbol x e |> Option.map (fun f -> Generic(f,ty))
        | Definition(a,b) -> 
            maybe {
                let! a' = removeSymbol x a  
                let! b' = removeSymbol x b 
                return Definition(a', b')} 
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
        | Definition(a,b)
        | Power(a, b) -> findVariables a |> Hashset.union (findVariables b)
        | IsFunctionExprAny(_,x,Some b) -> Hashset([x]) |> Hashset.union (findVariables b)
        | IsFunctionExprAny(_,x,_) -> Hashset([x])
        | Product l | Sum l | FunctionN(_, l) ->
            Hashset(Seq.collect findVariables l)
        | Generic(x,_)
        | Id x
        | Function(_, x) -> findVariables x
        | _ -> Hashset []

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


module Rational = 
    let rec simplifyNumbersAux (minval) (roundto : int) =
        function
        | Approximation (Approximation.Real r) ->
            Approximation (Approximation.Real (round roundto r))
        | Number n as num ->
            let f = float n
            let pf = abs f
            if pf > 10000. || pf < minval then
                let p10 = floor (log10 pf)
                let x = Math.Round(f / 10. ** p10, roundto) |> Expression.fromFloat
                Product [ x
                          Power(10Q, p10 |> Expression.fromFloat) ]
            else num
        | Power(x, n) -> Power(simplifyNumbersAux minval roundto x, n)
        | Sum l -> Sum(List.map (simplifyNumbersAux minval roundto) l)
        | Product l -> Product(List.map (simplifyNumbersAux minval roundto) l)
        | Function(f, x) -> Function(f, simplifyNumbersAux minval roundto x)
        | x -> x

    let rec simplifyNumbers(roundto : int) = simplifyNumbersAux 0.0001 roundto

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
    
    let Pi = Constants.pi  

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
        | IsRealNumber n -> 
            IntSharp.Types.Interval.FromDoubleWithEpsilonInflation (n.ToFloat().Value)
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
            | l' when (l' |> List.forall Expression.isRealNumber) ->
                let largest = l' |> List.map (fun x -> x.ToFloat().Value) |> List.max
                IntSharp.Types.Interval.FromDoubleWithEpsilonInflation largest
                |> Some
            | _ -> None
        | _ -> None
    replace e     
     

type Px () =
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
   
let makefunc f =
    match f with
    | IsFunctionExpr(_, xvar,fx) -> 
        fun x -> replaceSymbol x xvar fx
    | _ -> failwith "Not a function, use makefuncAlt instead"

let makefuncAlt xvar f =  
    fun x -> replaceSymbol x xvar f 

let applyfn f x = makefunc f x

module private Ops =
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
    static member min(a,b) = Ops.min2 a b
    
    

