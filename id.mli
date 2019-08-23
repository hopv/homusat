(* identifiers *)

type t = int

module IdSet : Set.S with type elt = t
module IdMap : X.Map.S with type key = t

val gen : t -> t (* generate a new identifier from existing one *)
val gen_var : string -> t (* generate a new identifier from a string *)
val of_string : string -> t (* get the common identifier of each string *)
val to_string : t -> string
