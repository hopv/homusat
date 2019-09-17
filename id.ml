(* Identifiers *)

type t = int

module IdSet = X.Set.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)
module IdMap = X.Map.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)

module OfStr = X.Map.Make (String)
module ToStr = X.Map.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)

let counter = ref 0
let of_str = ref OfStr.empty
let to_str = ref ToStr.empty

(* Generate a fresh identifier from an existing one *)
let gen = fun id ->
    let id' = !counter in
    let str = ToStr.find id !to_str in
    to_str := ToStr.add id' str !to_str;
    counter := !counter + 1;
    id'

(* Generate a fresh identifier from a string *)
let gen_var = fun str ->
    let id = !counter in
    to_str := ToStr.add id str !to_str;
    counter := !counter + 1;
    id

(* Get the common identifier of each string *)
let of_string = fun str ->
    if OfStr.mem str !of_str then
        OfStr.find str !of_str
    else begin
        let id = !counter in
        of_str := OfStr.add str id !of_str;
        to_str := ToStr.add id str !to_str;
        counter := !counter + 1;
        id
    end

let to_string = fun id ->
    if !Flags.debug_mode then
        (ToStr.find id !to_str) ^ "." ^ (string_of_int id)
    else
        ToStr.find id !to_str
