//This is a design for a computer language (called Reckoner) that's an actual tool for thought. It's a boolean algebraic language which allows you to compose logical inferences and perform inference on them. The language quietly leverages the Curry Howard isomorphism. 

type Value = 
 | True 
 | False
 | Unknown

type LogicExpr =
 | Constant of Value
 | Symb of string 
 | IfThen of LogicExpr * LogicExpr
 | IffThen of LogicExpr * LogicExpr
 | Not of LogicExpr
 | And of LogicExpr list 
 | Or of LogicExpr list with  
    static member (+) (a:LogicExpr, b:LogicExpr) = Or [a;b]
    static member (*) (a:LogicExpr, b:LogicExpr) = And [a;b]
    static member (<=>) (a:LogicExpr, b:LogicExpr) = IffThen(a,b) 


module LogicExpr =
    let toList = function 
        | Or l
        | And l -> l
        | _ -> []

    let isAnd = function  
        | And l -> true 
        | _ -> false

    let isOr = function 
        | Or _ -> true 
        | _ -> false 

let ifthen a b = IfThen (a,b)

let (!) s = Symb s

let (=>) a b = ifthen a b

let (==>) a b = ifthen (Symb a) (Symb b)

let (<==>) a b = Symb a <=> Symb b

let deMorgansLaw = function 
    | Not(Or l) -> And (List.map Not l)
    | Not(And l) -> Or (List.map Not l)
    | Or l
    | And l as f when List.forall (function Not _ -> true | _ -> false) l-> 
        let l' = List.map (function Not l -> l | _ -> failwith "error") l
        match f with 
        | And _ -> Not (Or l')
        | Or _ -> Not (And l')
        | f -> f
    | f -> f

let a,b = !"a", !"b"

deMorgansLaw (Not (a + b))
|> deMorgansLaw

let collectNestedSumOrProduct test l =
    let innersums, rest = List.partition test l
    let ls = List.collect LogicExpr.toList innersums
    ls @ rest

let rec simplify =
    function
    | Or l -> Or(List.map simplify (collectNestedSumOrProduct LogicExpr.isOr l))
    | And l -> And(List.map simplify (collectNestedSumOrProduct LogicExpr.isAnd l))
    | f -> f

Constant True => Constant False

let [a;b;c;d;e;f;g;h] =  List.map (string >> Symb) ['a'..'h']

a * b => c * d
b => e
b * c => f
f * g => h

a <=> b

"c" <==> "d"

!"brain is computable" => (!"mental judgment" => !"computable")
!"recognize intelligence" => !"mental judgment"

(!"recognize intelligence" => !"intelligent") + (!"intelligent" => !"recognize intelligence")

!"easily computable"
!"hard to compute; PSPACE"
!"easy judgment"
(!"easily computable" * !"hard to compute; PSPACE") => (!"brain has PSPACE hacks" + !"lots of exploitable structure")
!""

(*if vampire then consumes blood; if person bitten by vampire then person vampire ; beth bitten by vampire *)
(!"c" * !"d") + Symb "a" + Symb "b" |> simplify
(* 
time slowed why?

things that can cause time to slow down are:

if time slowed then gravitational field increase or traveled near speed of light and accelerated to return if traveled near speed of light and accelerated to return then went on a journey if gravitational field disturbed then orbits affected if gravitational field disturbed then gravitational field increase or gravitational field decrease*)
c * d
