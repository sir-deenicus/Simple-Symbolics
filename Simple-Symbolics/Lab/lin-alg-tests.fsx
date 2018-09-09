#load "linear-algebra.fsx"
open ``Linear-algebra``
open Core.Vars
open MathNet.Symbolics

dot [a ; b] [cos a;b] |> Infix.format //|> Evaluate.evaluate symbols2
 
matrixvec [a; b] [[a;b];[c;d]] |> List.map Infix.format 


