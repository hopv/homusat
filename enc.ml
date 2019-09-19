(* Encoding of (sub)formulas as integers *)

type elt = int

type formula =
    | Or of elt list
    | And of elt list
    | Box of LTS.label * elt
    | Diamond of LTS.label * elt
    | App of Id.t * (elt list)

type func = HFS.fp * Id.t * HFS.simple_type * (HFS.argument list) * elt

type t = func list

module FmlMap = X.Map.Make (struct
    type t = formula
    let compare : t -> t -> int = compare
end)

let counter = ref 0
let encoder = ref FmlMap.empty
let decoder = ref [| |] (* IntMap.empty *)

let register = fun fml ->
    if FmlMap.mem fml !encoder then
        FmlMap.find fml !encoder
    else begin
        let ret = !counter in
        encoder := FmlMap.add fml ret !encoder;
        counter := ret + 1;
        ret
    end

let rec encode_fml = fun fml ->
    let fml =
        match fml with
        | HFS.Or (xs) -> Or (X.List.map encode_fml xs)
        | HFS.And (xs) -> And (X.List.map encode_fml xs)
        | HFS.Box (a, x) -> Box (a, encode_fml x)
        | HFS.Diamond (a, x) -> Diamond (a, encode_fml x)
        | HFS.App (x, ys) -> App (x, X.List.map encode_fml ys)
    in
    register fml

let init_decoder = fun () ->
    let f = fun y x -> !decoder.(x) <- y in
    decoder := Array.make !counter (Or ([]));
    FmlMap.iter f !encoder

let encode = fun funcs ->
    let f = fun func ->
        let (fp, x, t, args, body) = func in
        let body = encode_fml body in
        (fp, x, t, args, body)
    in
    let funcs = X.List.map f funcs in
    init_decoder ();
    funcs

let decode = fun x -> !decoder.(x)

let rec decode_fml = fun fml ->
    match decode fml with
    | Or (xs) -> HFS.Or (X.List.map decode_fml xs)
    | And (xs) -> HFS.And (X.List.map decode_fml xs)
    | Box (a, x) -> HFS.Box (a, decode_fml x)
    | Diamond (a, x) -> HFS.Diamond (a, decode_fml x)
    | App (x, ys) -> HFS.App (x, X.List.map decode_fml ys)

let string_of_formula = fun fml ->
    HFS.string_of_formula (decode_fml fml)
