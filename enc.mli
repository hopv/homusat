(* Encode formulas as integers *)

type elt = int

type formula =
    | Or of elt list
    | And of elt list
    | Box of LTS.label * elt
    | Diamond of LTS.label * elt
    | App of Id.t * (elt list)

type func = HFS.fp * Id.t * HFS.simple_type * (HFS.argument list) * elt

type t = func list

val encode : HFS.t -> t
val decode : elt -> formula
val string_of_formula : elt -> string
