  
module MathNet.Symbolics.OEIS

open System
open MathNet.Numerics
open NumberProperties 
open FSharp.Data
 
let [<Literal>] oeisjsonpath = __SOURCE_DIRECTORY__  +  "/oeis-search.json"
type OEIntegerSequences = JsonProvider<oeisjsonpath> //OEISjson.json> //, EmbeddedResource="Simple-Symbolics, oeis-search.json"

type OEIS() =
    static member query (str: string) =
        let url = sprintf "http://oeis.org/search?fmt=json&q=%s" str
        use wc = new Net.WebClient()

        let res = wc.DownloadString url |> OEIntegerSequences.Parse

        if res.Count = 0 then None else res.Results |> Some

    static member query (nums: int seq) =
        let str =
            nums
            |> Seq.map string
            |> String.concat ","
        OEIS.query str

    static member query (nums: BigRational seq) =
        let strnums =
            nums
            |> Seq.map (fun r -> string r.Numerator)
            |> String.concat ","
        let strdens =
            nums
            |> Seq.map (fun r -> string r.Denominator)
            |> String.concat ","

        let r1 = OEIS.query strnums
        let r2 = OEIS.query strdens
        r1, r2

    static member query (nums: Expression seq) =
        [ for n in nums do
            match Expression.toRational n with
            | Some n -> yield n
            | _ -> () ]
        |> OEIS.query