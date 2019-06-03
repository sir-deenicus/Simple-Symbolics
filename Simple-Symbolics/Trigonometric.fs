module MathNet.Symbolics.Trigonometric

 
let doubleAngleIdentity2a = function
    | Function(Cos, Product[n; x]) when n = 2Q -> 2 * (cos x) ** 2 - 1
    | f -> f