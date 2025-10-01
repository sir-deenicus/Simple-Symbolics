namespace MathNet.Symbolics

//TODO: review implementation

module AutoDiff =
    open MathNet.Symbolics
    open Operators
    open MathNet.Symbolics.Core
    open System.Collections.Generic

    type Dual = { v: Expression; dv: Expression }

    let inline mk v dv = { v = v; dv = dv }

    let rec dual (x: Expression) focus =
        match x with
        | Identifier _ when x = focus -> mk x 1Q
        | Identifier _ -> mk x 0Q
        | Number _ -> mk x 0Q
        | Sum terms ->
            terms
            |> List.map (fun t -> dual t focus)
            |> List.reduce (fun a b -> mk (a.v + b.v) (a.dv + b.dv))
        | Product terms ->
            // derivative of product: sum_i ( (Π_{j≠i} vj) * dvi )
            let ds = terms |> List.map (fun t -> dual t focus)
            let prodAll = ds |> List.map (fun d -> d.v) |> List.reduce (*)
            let dv =
                ds
                |> List.mapi (fun i di ->
                    let others =
                        ds
                        |> List.mapi (fun j dj -> if i = j then 1Q else dj.v)
                        |> List.reduce (*)
                    others * di.dv)
                |> List.reduce (+)
            mk prodAll dv
        | Power (b, p) ->
            // b^p * (p' * ln b + p * b'/b)
            let db = dual b focus
            let dp = dual p focus
            let v = b ** p
            let dv = v * (dp.dv * (ln db.v) + dp.v * db.dv / db.v)
            mk v dv
        | Function(Exp, a) ->
            let da = dual a focus
            mk (exp da.v) (exp da.v * da.dv)
        | Function(Ln, a) ->
            let da = dual a focus
            mk (ln da.v) (da.dv / da.v)
        | Function(Sin, a) ->
            let da = dual a focus
            mk (sin da.v) (cos da.v * da.dv)
        | Function(Cos, a) ->
            let da = dual a focus
            mk (cos da.v) (-sin da.v * da.dv)
        | Function(Tan, a) ->
            let da = dual a focus
            mk (tan da.v) ((sec da.v) ** 2Q * da.dv)
            
        | Function(_, _) ->
            // Fallback to symbolic diff for any unhandled unary function
            mk x (Calculus.differentiate2 focus x |> Expression.simplify)
        | FunctionN(_, _) ->
            mk x (Calculus.differentiate2 focus x |> Expression.simplify)
        | _ ->
            mk x (Calculus.differentiate2 focus x |> Expression.simplify)

    let differentiate focus expr =
        let r = dual expr focus
        r.dv |> Expression.simplify


    
    // ---------- Reverse mode via closures ----------
    // BackOp mutates an in-flight derivative dictionary.
    type BackOp = Dictionary<Expression, Expression> -> unit

    let private addContribution (dict: Dictionary<Expression, Expression>) key delta =
        if delta = 0Q then ()
        else
            match dict.TryGetValue key with
            | true, prev -> dict[key] <- Expression.simplify (prev + delta)
            | _ -> dict[key] <- delta

    let reverseDifferentiate (focus: Expression) (expr: Expression) =
        let ops = ResizeArray<BackOp>()

        // Visit builds closures post-order (children first, then node)
        let rec visit (e: Expression) =
            match e with
            | Number _
            | Identifier _ -> ()
            | Sum terms ->
                terms |> List.iter visit
                ops.Add(fun d ->
                    let upstream =
                        match d.TryGetValue e with
                        | true, u -> u
                        | _ -> 0Q
                    if upstream <> 0Q then
                        for t in terms do addContribution d t upstream)
            | Product terms ->
                terms |> List.iter visit
                let n = List.length terms
                // Precompute prefix/suffix products to form product of others
                let arr = terms |> List.toArray
                let prefix = Array.zeroCreate n
                let suffix = Array.zeroCreate n
                prefix[0] <- arr[0]
                for i in 1 .. n - 1 do prefix[i] <- prefix[i-1] * arr[i]
                suffix[n-1] <- arr[n-1]
                for i = n-2 downto 0 do suffix[i] <- suffix[i+1] * arr[i] 

                ops.Add(fun d ->
                    let upstream =
                        match d.TryGetValue e with
                        | true, u -> u
                        | _ -> 0Q
                    if upstream <> 0Q then
                        for i in 0 .. n - 1 do
                            let others =
                                if n = 1 then 1Q
                                elif i = 0 then suffix[1]
                                elif i = n - 1 then prefix[n-2]
                                else prefix[i-1] * suffix[i+1]
                            addContribution d arr[i] (upstream * others))
            | Power (b, p) ->
                visit b
                visit p
                ops.Add(fun d ->
                    let upstream =
                        match d.TryGetValue e with
                        | true, u -> u
                        | _ -> 0Q
                    if upstream <> 0Q then
                        // derivative wrt base
                        addContribution d b (upstream * p * (b ** (p - 1Q)))
                        // derivative wrt exponent
                        addContribution d p (upstream * (b ** p) * ln b))
            | Function(Exp, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q -> addContribution d a (u * exp a)
                    | _ -> ())
            | Function(Ln, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q -> addContribution d a (u / a)
                    | _ -> ())
            | Function(Sin, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q -> addContribution d a (u * cos a)
                    | _ -> ())
            | Function(Cos, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q -> addContribution d a (u * -sin a)
                    | _ -> ())
            | Function(Tan, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q -> addContribution d a (u * (sec a) ** 2Q)
                    | _ -> ())
            | Function(Asin, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q ->
                        addContribution d a (u / sqrt (1Q - a ** 2Q))
                    | _ -> ())
            | Function(Acos, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q ->
                        addContribution d a (-u / sqrt (1Q - a ** 2Q))
                    | _ -> ())
            | Function(Atan, a) ->
                visit a
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q ->
                        addContribution d a (u / (1Q + a ** 2Q))
                    | _ -> ())
            | FunctionN(Log, [ b; x ]) ->
                // log base b of x
                visit b
                visit x
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q ->
                        // d/dx
                        addContribution d x (u / (x * ln b))
                        // d/db
                        addContribution d b (u * -(ln x) / (ln b) ** 2Q * (1Q / b))
                    | _ -> ())
            | Function(op, a) ->
                // Generic unary fallback: compute d/d(a) (op a) symbolically.
                visit a
                let placeholder = Identifier (Symbol "__u")          // unique temp symbol
                let proto = Function(op, placeholder)
                // derivative of proto w.r.t placeholder, then substitute placeholder -> a
                let dproto =
                    Calculus.differentiate2 placeholder proto
                    |> Expression.replace ([ placeholder, a ])
                    |> Expression.simplify
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q ->
                        addContribution d a (u * dproto)
                    | _ -> ())
            | FunctionN(op, args) ->
                // Generic n-ary fallback. Treat each argument independently: need ∂/∂arg_i (op args)
                // Build proto with fresh placeholders, differentiate w.r.t each, substitute back.
                let placeholders =
                    args
                    |> List.mapi (fun i _ -> Identifier (Symbol (sprintf "__u%d" i)))
                List.iter visit args
                let proto = FunctionN(op, placeholders)
                let partials =
                    placeholders
                    |> List.map (fun ph ->
                        let dph =
                            Calculus.differentiate2 ph proto
                            |> Expression.replace (List.zip placeholders args)
                            |> Expression.simplify
                        dph)
                let argsArray = List.toArray args
                let partsArray = List.toArray partials
                ops.Add(fun d ->
                    match d.TryGetValue e with
                    | true, u when u <> 0Q ->
                        for i = 0 to argsArray.Length - 1 do
                            let contrib = u * partsArray[i]
                            if contrib <> 0Q then addContribution d argsArray[i] contrib
                    | _ -> ())
            | _ -> ()

        visit expr

        // derivative accumulators
        let grads = Dictionary<Expression, Expression>(HashIdentity.Structural)
        grads[expr] <- 1Q

        // Apply closures in reverse (root first)
        for i = ops.Count - 1 downto 0 do
            ops[i] grads

        // If any generic unhandled functions existed above, they won't have propagated;
        // so fall back to direct diff for those parts when focus present but gradient missing.
        match grads.TryGetValue focus with
        | true, g -> Expression.simplify g
        | _ ->
            // fallback to direct symbolic diff (still simplifed)
            Calculus.differentiate2 focus expr |> Expression.simplify