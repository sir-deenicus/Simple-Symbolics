namespace MathNet.Symbolics

open MathNet.Symbolics.Core
open Utils
open Core

type Tropicalf (e:float) =
    member __.Value = e
    static member (+) (l : Tropicalf, r : Tropicalf) =
        Tropicalf(min l.Value r.Value)
    static member (+) (l : Tropicalf, r : float) =
        Tropicalf(min l.Value r)
    static member (+) (l : float, r : Tropicalf) =
        Tropicalf(min l r.Value)
    static member (*) (l : Tropicalf, r : Tropicalf) =
        Tropicalf(l.Value + r.Value)
    static member (*) (l : Tropicalf, r : float) =
        Tropicalf(l.Value + r)
    static member (*) (l : float, r : Tropicalf) =
        Tropicalf(l + r.Value)
    override __.ToString() = string e

type Tropical (e:Expression) =
    member __.Value = Expression.simplifyLite e
    static member (+) (l : Tropical, r : Tropical) =
        Tropical(Ops.min2 l.Value r.Value)
    static member (+) (l : Tropical, r : float) =
        Tropical(Ops.min2 l.Value (real r))
    static member (+) (l : float, r : Tropical) =
        Tropical(Ops.min2 (real l) r.Value)
    static member (+) (l : Expression, r : Tropical) =
        Tropical(Ops.min2 l r.Value)
    static member (+) (l : Tropical, r : Expression) =
        Tropical(Ops.min2 l.Value r)
    static member (+) (l : Tropical, r : int) =
        Tropical(Ops.min2 l.Value (Expression.FromInt32 r))
    static member (+) (l : int, r : Tropical) =
        Tropical(Ops.min2 (Expression.FromInt32 l) r.Value)

    static member (*) (l : Tropical, r : Tropical) =
        Tropical(l.Value + r.Value)
    static member (*) (l : Tropicalf, r : float) =
        Tropical(l.Value + real r)
    static member (*) (l : float, r : Tropical) =
        Tropical(l + r.Value)
    static member (*) (l : Expression, r : Tropical) =
        Tropical(l + r.Value)
    static member (*) (l : Tropical, r : Expression) =
        Tropical(l.Value + r) 
    static member (*) (l : Tropical, r : int) =
        Tropical(l.Value + (Expression.FromInt32 r))
    static member (*) (l : int, r : Tropical) =
        Tropical((Expression.FromInt32 l) + r.Value)

    override t.ToString() = fmt (t.Value)
    static member One = Tropical(0Q)
    static member Zero = Tropical(PositiveInfinity)
    static member Pow(t:Tropical, n:int) =
        List.replicate n t.Value |> List.sum |> Tropical  
    new(e:int) = Tropical(Expression.FromInt32 e)

module Tropical =
    let tr (e:Expression) = Tropical e