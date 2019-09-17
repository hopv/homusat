(* Identifiers *)

type t = int

module IdSet : X.Set.S with type elt = t
module IdMap : X.Map.S with type key = t

val gen : t -> t (* Generate a fresh identifier from an existing one *)
val gen_var : string -> t (* Generate a fresh identifier from a string *)
val of_string : string -> t (* Get the common identifier of each string *)
val to_string : t -> string
