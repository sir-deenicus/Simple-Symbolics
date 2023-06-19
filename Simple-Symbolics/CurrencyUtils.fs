module MathNet.Symbolics.Currencies
  
open MathNet.Symbolics.Utils
open System
open Prelude.Common 
open FSharp.Data  

let currencycacheloc = "currencycache.json"

let [<Literal>] CurrencyTemplate = """{"baseCountry":"US","baseCurrency":"USD","rates":[{"id":432,"name":"Nigeria","name_zh":"尼日利亚","code":"NG","currency_name":"Naira","currency_name_zh":"尼日利亚奈拉","currency_code":"NGN","rate":362.63,"hits":22345,"selected":0,"top":0},{"id":449,"name":"Singapore","name_zh":"新加坡","code":"SG","currency_name":"Dollar","currency_name_zh":"新币","currency_code":"SGD","rate":1.3909,"hits":1115270,"selected":0,"top":0}]}"""

type CurrencyProvider = FSharp.Data.JsonProvider<CurrencyTemplate>
 
let downloadCurrencyRates(useDir) =
    use wc = new Net.WebClient()
    let currencycachepath = pathCombine useDir currencycacheloc
    try
        let data =
            wc.DownloadData "https://www.mycurrency.net/US.json"
            |> String.decodeFromUtf8Bytes
        IO.File.WriteAllText(currencycachepath, data)
        data
        |> CurrencyProvider.Parse
        |> Some
    with _ -> 
        if IO.File.Exists currencycachepath then
            IO.File.ReadAllText currencycachepath
            |> CurrencyProvider.Parse
            |> Some
        else None

let buildCurrencyMap(useDir) =
    match downloadCurrencyRates(useDir) with
    | None -> Dict()
    | Some currencyRates ->
        currencyRates.Rates
        |> Array.map (fun r ->
                r.CurrencyCode,
                (1M / r.Rate)
                |> float
                |> smartround2 2)
        |> Dict.ofSeq        

let mutable currencyMap = Dict()

let rebuildCurrencyMap(dir) = currencyMap <- buildCurrencyMap dir
  
let checkCurrency eps c = 
    match currencyMap.tryFind c with 
    | None -> nan
    | Some v -> v + eps

type WorldBankHelper() =
    let data = WorldBankData.GetDataContext()
    member t.Countries = data.Countries

let getGDPperCapita (c:WorldBankData.ServiceTypes.Country) =
    c.Indicators
        .``GDP per capita, PPP (current international $)`` 
        |> Seq.last

let getGDPperCapitaPP (c:WorldBankData.ServiceTypes.Country) =
    c.Indicators
        .``GDP per capita, PPP (current international $)`` 
        |> Seq.last

module Units =
    open Units
    open MathNet.Symbolics.Core
     
    let setCurrency eps curr = 
        (checkCurrency eps curr) * usd |> setAlt curr
    
    let currencyFriction = 1e-04

    let mutable ngn = setCurrency 1e-04 "NGN"
    let mutable gbp = setCurrency 8e-03 "GBP"
    let mutable eur = setCurrency currencyFriction "EUR"


    let redoCurrencyConversions () = 
        ngn <- setCurrency 1e-04 "NGN"
        gbp <- setCurrency 8e-03 "GBP"
        eur <- setCurrency currencyFriction "EUR"

    let convertCurrencyWeightedByGDPPCPP (sourcecountry:WorldBankData.ServiceTypes.Country) (targetcountry:WorldBankData.ServiceTypes.Country) (s:Units) =
        if s.Unit = usd.Unit then 
            let _, gdpsource = getGDPperCapitaPP sourcecountry  
            let _, gdptarget = getGDPperCapitaPP targetcountry 
            s.Quantity/gdpsource * gdptarget * usd
        else failwith "Not a currency"